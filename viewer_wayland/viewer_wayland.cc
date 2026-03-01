// Pure Wayland viewer — no GLFW, no Vulkan, no external deps beyond lightrt + Wayland
// Wayland + xkbcommon loaded at runtime via dlopen — no libwayland-dev or
// libxkbcommon-dev needed at compile time.

#include "wayland/lightrt_wayland.h"
#include "wayland/lightrt_xdg_shell.h"
#define LIGHTRT_WAYLAND_IMPLEMENTATION
#include "wayland/lightrt_wayland_loader.h"

#include "common/viewer_common.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <poll.h>

#if defined(__linux__)
#include <linux/memfd.h>
#include <sys/syscall.h>
#endif

using namespace lightrt_viewer;

// --- Globals ---
static ViewerState g_state;
static bool        g_running    = true;
static bool        g_configured = false;

// Wayland objects
static struct wl_display     *g_display     = nullptr;
static struct wl_compositor  *g_compositor  = nullptr;
static struct wl_shm         *g_shm         = nullptr;
static struct xdg_wm_base   *g_xdg_wm_base = nullptr;
static struct wl_seat        *g_seat        = nullptr;
static struct wl_surface     *g_surface     = nullptr;
static struct xdg_surface    *g_xdg_surface = nullptr;
static struct xdg_toplevel   *g_toplevel    = nullptr;
static struct wl_keyboard    *g_keyboard    = nullptr;
static struct wl_pointer     *g_pointer     = nullptr;

// xkbcommon state
static struct xkb_context *g_xkb_ctx     = nullptr;
static struct xkb_keymap  *g_xkb_keymap  = nullptr;
static struct xkb_state   *g_xkb_state   = nullptr;

// Shared memory buffers (double-buffered)
static int              g_shm_fd       = -1;
static void            *g_shm_data     = nullptr;
static size_t           g_shm_size     = 0;
static struct wl_buffer *g_buffers[2]  = {};
static bool             g_buffer_busy[2] = {};
static int              g_current_buffer = 0;

// --- File loading ---

static void LoadAndReplaceScene(const std::string& path) {
    std::cout << "Loading " << path << "...\n";
    scene::Scene newScene;
    if (!LoadModel(path, newScene)) {
        std::cerr << "Failed to load: " << path << "\n";
        return;
    }
    if (sceneTriangleCount(newScene) == 0) {
        std::cerr << "No triangles in: " << path << "\n";
        return;
    }
    g_state.scene = std::move(newScene);
    FitToScene(g_state);
    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << sceneTriangleCount(g_state.scene) << " triangles.\n";

    // Update window title
    size_t sep = path.find_last_of("/\\");
    std::string fname = (sep != std::string::npos) ? path.substr(sep + 1) : path;
    if (g_toplevel)
        xdg_toplevel_set_title(g_toplevel, ("LightRT Viewer (Wayland) - " + fname).c_str());
}

static void ShowOpenFileDialog() {
    // Try zenity (GNOME/GTK), then kdialog (KDE)
    FILE* f = popen("zenity --file-selection --title='Open File' 2>/dev/null", "r");
    if (!f) f = popen("kdialog --getopenfilename . 2>/dev/null", "r");
    if (!f) {
        std::cerr << "No file dialog available — install zenity or kdialog\n";
        return;
    }
    char buf[4096] = {};
    if (fgets(buf, sizeof(buf), f)) {
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
        if (buf[0] != '\0') LoadAndReplaceScene(buf);
    }
    pclose(f);
}

// --- Timing helpers ---

static uint64_t GetTimeNs() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

// --- Anonymous shared memory fd ---

static int create_shm_fd(void) {
#if defined(__linux__) && defined(SYS_memfd_create)
    int fd = (int)syscall(SYS_memfd_create, "lightrt-wayland", MFD_CLOEXEC);
    if (fd >= 0) return fd;
#endif
    // Fallback: shm_open + shm_unlink
    char name[] = "/lightrt-wl-XXXXXX";
    uint64_t t = GetTimeNs();
    for (int i = 0; i < 6; i++) {
        name[12 + i] = 'A' + (char)(t % 26);
        t /= 26;
    }
    int fd2 = shm_open(name, O_RDWR | O_CREAT | O_EXCL, 0600);
    if (fd2 >= 0) shm_unlink(name);
    return fd2;
}

// --- Buffer management ---

static void destroy_buffers(void) {
    for (int i = 0; i < 2; i++) {
        if (g_buffers[i]) {
            wl_buffer_destroy(g_buffers[i]);
            g_buffers[i] = nullptr;
        }
        g_buffer_busy[i] = false;
    }
    if (g_shm_data) {
        munmap(g_shm_data, g_shm_size);
        g_shm_data = nullptr;
    }
    if (g_shm_fd >= 0) {
        close(g_shm_fd);
        g_shm_fd = -1;
    }
    g_shm_size = 0;
}

static void buffer_release(void * /*data*/, struct wl_buffer *buffer) {
    for (int i = 0; i < 2; i++) {
        if (g_buffers[i] == buffer) {
            g_buffer_busy[i] = false;
            break;
        }
    }
}

static const struct wl_buffer_listener buffer_listener = {
    buffer_release,
};

static bool create_buffers(uint32_t width, uint32_t height) {
    destroy_buffers();

    int32_t stride = (int32_t)(width * 4);
    size_t buf_size = (size_t)stride * height;
    g_shm_size = buf_size * 2; // double buffer

    g_shm_fd = create_shm_fd();
    if (g_shm_fd < 0) {
        std::cerr << "Failed to create shared memory fd.\n";
        return false;
    }

    if (ftruncate(g_shm_fd, (off_t)g_shm_size) < 0) {
        std::cerr << "Failed to resize shared memory.\n";
        close(g_shm_fd);
        g_shm_fd = -1;
        return false;
    }

    g_shm_data = mmap(nullptr, g_shm_size, PROT_READ | PROT_WRITE,
                       MAP_SHARED, g_shm_fd, 0);
    if (g_shm_data == MAP_FAILED) {
        std::cerr << "Failed to mmap shared memory.\n";
        g_shm_data = nullptr;
        close(g_shm_fd);
        g_shm_fd = -1;
        return false;
    }

    struct wl_shm_pool *pool = wl_shm_create_pool(g_shm, g_shm_fd,
                                                    (int32_t)g_shm_size);
    if (!pool) {
        std::cerr << "Failed to create wl_shm_pool.\n";
        destroy_buffers();
        return false;
    }

    for (int i = 0; i < 2; i++) {
        g_buffers[i] = wl_shm_pool_create_buffer(pool,
            (int32_t)(buf_size * (size_t)i),
            (int32_t)width, (int32_t)height, stride,
            WL_SHM_FORMAT_XRGB8888);
        if (!g_buffers[i]) {
            std::cerr << "Failed to create wl_buffer[" << i << "].\n";
            wl_shm_pool_destroy(pool);
            destroy_buffers();
            return false;
        }
        wl_buffer_add_listener(g_buffers[i], &buffer_listener, nullptr);
    }

    wl_shm_pool_destroy(pool);
    g_current_buffer = 0;
    return true;
}

// --- Wayland event handlers ---

// Registry

static void registry_global(void * /*data*/, struct wl_registry *registry,
                             uint32_t name, const char *interface,
                             uint32_t version) {
    if (strcmp(interface, "wl_compositor") == 0) {
        g_compositor = (struct wl_compositor *)
            wl_registry_bind(registry, name, &wl_compositor_interface,
                             version < 4 ? version : 4);
    } else if (strcmp(interface, "wl_shm") == 0) {
        g_shm = (struct wl_shm *)
            wl_registry_bind(registry, name, &wl_shm_interface, 1);
    } else if (strcmp(interface, "xdg_wm_base") == 0) {
        g_xdg_wm_base = (struct xdg_wm_base *)
            wl_registry_bind(registry, name, &xdg_wm_base_interface,
                             version < 2 ? version : 2);
    } else if (strcmp(interface, "wl_seat") == 0) {
        g_seat = (struct wl_seat *)
            wl_registry_bind(registry, name, &wl_seat_interface,
                             version < 5 ? version : 5);
    }
}

static void registry_global_remove(void * /*data*/,
                                    struct wl_registry * /*registry*/,
                                    uint32_t /*name*/) {
    // Not handling dynamic removal for this viewer
}

static const struct wl_registry_listener registry_listener = {
    registry_global,
    registry_global_remove,
};

// XDG wm_base

static void xdg_wm_base_ping_handler(void * /*data*/,
                                       struct xdg_wm_base *wm_base,
                                       uint32_t serial) {
    xdg_wm_base_pong(wm_base, serial);
}

static const struct xdg_wm_base_listener wm_base_listener = {
    xdg_wm_base_ping_handler,
};

// XDG surface

static void xdg_surface_configure_handler(void * /*data*/,
                                            struct xdg_surface *surface,
                                            uint32_t serial) {
    xdg_surface_ack_configure(surface, serial);
    g_configured = true;
}

static const struct xdg_surface_listener xdg_surface_listener_impl = {
    xdg_surface_configure_handler,
};

// XDG toplevel

static void xdg_toplevel_configure_handler(void * /*data*/,
                                             struct xdg_toplevel * /*toplevel*/,
                                             int32_t width, int32_t height,
                                             struct wl_array * /*states*/) {
    if (width > 0 && height > 0 &&
        ((uint32_t)width != g_state.width ||
         (uint32_t)height != g_state.height)) {
        ResizeFramebuffer(g_state, (uint32_t)width, (uint32_t)height);
        create_buffers((uint32_t)width, (uint32_t)height);
    }
}

static void xdg_toplevel_close_handler(void * /*data*/,
                                         struct xdg_toplevel * /*toplevel*/) {
    g_running = false;
}

static void xdg_toplevel_configure_bounds_handler(
    void * /*data*/, struct xdg_toplevel * /*toplevel*/,
    int32_t /*width*/, int32_t /*height*/) {
    // Informational only
}

static void xdg_toplevel_wm_capabilities_handler(
    void * /*data*/, struct xdg_toplevel * /*toplevel*/,
    struct wl_array * /*capabilities*/) {
    // Informational only
}

static const struct xdg_toplevel_listener toplevel_listener = {
    xdg_toplevel_configure_handler,
    xdg_toplevel_close_handler,
    xdg_toplevel_configure_bounds_handler,
    xdg_toplevel_wm_capabilities_handler,
};

// Keyboard

static void keyboard_keymap(void * /*data*/,
                              struct wl_keyboard * /*keyboard*/,
                              uint32_t format, int32_t fd, uint32_t size) {
    if (format != WL_KEYBOARD_KEYMAP_FORMAT_XKB_V1) {
        close(fd);
        return;
    }

    char *map_str = (char *)mmap(nullptr, size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (map_str == MAP_FAILED) return;

    if (g_xkb_state) { xkb_state_unref(g_xkb_state); g_xkb_state = nullptr; }
    if (g_xkb_keymap) { xkb_keymap_unref(g_xkb_keymap); g_xkb_keymap = nullptr; }

    g_xkb_keymap = xkb_keymap_new_from_string(g_xkb_ctx, map_str,
        XKB_KEYMAP_FORMAT_TEXT_V1, XKB_KEYMAP_COMPILE_NO_FLAGS);
    munmap(map_str, size);

    if (g_xkb_keymap) {
        g_xkb_state = xkb_state_new(g_xkb_keymap);
    }
}

static void keyboard_enter(void * /*data*/,
                             struct wl_keyboard * /*keyboard*/,
                             uint32_t /*serial*/,
                             struct wl_surface * /*surface*/,
                             struct wl_array * /*keys*/) {
}

static void keyboard_leave(void * /*data*/,
                             struct wl_keyboard * /*keyboard*/,
                             uint32_t /*serial*/,
                             struct wl_surface * /*surface*/) {
    // Clear all modifiers when leaving
    g_state.shiftPressed = false;
    g_state.ctrlPressed  = false;
    g_state.altPressed   = false;
    g_state.tabPressed   = false;
}

static void keyboard_key(void * /*data*/,
                           struct wl_keyboard * /*keyboard*/,
                           uint32_t /*serial*/, uint32_t /*time*/,
                           uint32_t key, uint32_t state) {
    if (!g_xkb_state) return;

    // xkbcommon uses evdev offset: key + 8
    uint32_t sym = xkb_state_key_get_one_sym(g_xkb_state, key + 8);
    bool pressed = (state == WL_KEYBOARD_KEY_STATE_PRESSED);

    switch (sym) {
    case XKB_KEY_f: case XKB_KEY_F:
        g_state.keys[KEY_F] = pressed; break;
    case XKB_KEY_s: case XKB_KEY_S:
        g_state.keys[KEY_S] = pressed; break;
    case XKB_KEY_plus: case XKB_KEY_equal:
        g_state.keys[KEY_PLUS] = pressed; break;
    case XKB_KEY_o: case XKB_KEY_O:
        if (pressed) ShowOpenFileDialog(); break;
    case XKB_KEY_Escape:
        g_state.keys[KEY_ESCAPE] = pressed; break;
    case XKB_KEY_Shift_L: case XKB_KEY_Shift_R:
        g_state.shiftPressed = pressed; break;
    case XKB_KEY_Control_L: case XKB_KEY_Control_R:
        g_state.ctrlPressed = pressed; break;
    case XKB_KEY_Alt_L: case XKB_KEY_Alt_R:
        g_state.altPressed = pressed; break;
    case XKB_KEY_Tab:
        g_state.tabPressed = pressed; break;
    }
}

static void keyboard_modifiers(void * /*data*/,
                                 struct wl_keyboard * /*keyboard*/,
                                 uint32_t /*serial*/,
                                 uint32_t mods_depressed,
                                 uint32_t mods_latched,
                                 uint32_t mods_locked,
                                 uint32_t group) {
    if (g_xkb_state) {
        xkb_state_update_mask(g_xkb_state,
            mods_depressed, mods_latched, mods_locked, 0, 0, group);
    }
}

static void keyboard_repeat_info(void * /*data*/,
                                   struct wl_keyboard * /*keyboard*/,
                                   int32_t /*rate*/, int32_t /*delay*/) {
    // Not handling key repeat
}

static const struct wl_keyboard_listener keyboard_listener_impl = {
    keyboard_keymap,
    keyboard_enter,
    keyboard_leave,
    keyboard_key,
    keyboard_modifiers,
    keyboard_repeat_info,
};

// Pointer

static void pointer_enter(void * /*data*/, struct wl_pointer * /*pointer*/,
                            uint32_t /*serial*/,
                            struct wl_surface * /*surface*/,
                            wl_fixed_t /*sx*/, wl_fixed_t /*sy*/) {
}

static void pointer_leave(void * /*data*/, struct wl_pointer * /*pointer*/,
                            uint32_t /*serial*/,
                            struct wl_surface * /*surface*/) {
}

static void pointer_motion(void * /*data*/, struct wl_pointer * /*pointer*/,
                             uint32_t /*time*/,
                             wl_fixed_t sx, wl_fixed_t sy) {
    double x = wl_fixed_to_double(sx);
    double y = wl_fixed_to_double(sy);
    OnMouseDrag(g_state, x, y);
}

static void pointer_button(void * /*data*/, struct wl_pointer * /*pointer*/,
                              uint32_t /*serial*/, uint32_t /*time*/,
                              uint32_t button, uint32_t state) {
    bool pressed = (state == WL_POINTER_BUTTON_STATE_PRESSED);

    switch (button) {
    case BTN_LEFT:
        g_state.lmbPressed = pressed;
        if (pressed) {
            OnMouseDown(g_state, g_state.lastX, g_state.lastY);
        } else if (!g_state.mmbPressed && !g_state.rmbPressed) {
            g_state.dragging = false;
        }
        break;
    case BTN_MIDDLE:
        g_state.mmbPressed = pressed;
        if (pressed) {
            OnMouseDown(g_state, g_state.lastX, g_state.lastY);
        } else if (!g_state.lmbPressed && !g_state.rmbPressed) {
            g_state.dragging = false;
        }
        break;
    case BTN_RIGHT:
        g_state.rmbPressed = pressed;
        if (pressed) {
            OnMouseDown(g_state, g_state.lastX, g_state.lastY);
        } else if (!g_state.lmbPressed && !g_state.mmbPressed) {
            g_state.dragging = false;
        }
        break;
    }
}

static void pointer_axis(void * /*data*/, struct wl_pointer * /*pointer*/,
                           uint32_t /*time*/, uint32_t axis,
                           wl_fixed_t value) {
    if (axis == WL_POINTER_AXIS_VERTICAL_SCROLL) {
        double v = wl_fixed_to_double(value);
        // Wayland axis: positive = scroll down = zoom out
        DollyCamera(g_state, (float)(v * 0.03));
    }
}

static void pointer_frame(void * /*data*/,
                            struct wl_pointer * /*pointer*/) {
}

static void pointer_axis_source(void * /*data*/,
                                  struct wl_pointer * /*pointer*/,
                                  uint32_t /*axis_source*/) {
}

static void pointer_axis_stop(void * /*data*/,
                                struct wl_pointer * /*pointer*/,
                                uint32_t /*time*/, uint32_t /*axis*/) {
}

static void pointer_axis_discrete(void * /*data*/,
                                    struct wl_pointer * /*pointer*/,
                                    uint32_t /*axis*/, int32_t /*discrete*/) {
}

static void pointer_axis_value120(void * /*data*/,
                                    struct wl_pointer * /*pointer*/,
                                    uint32_t /*axis*/, int32_t /*value120*/) {
}

static void pointer_axis_relative_direction(void * /*data*/,
                                              struct wl_pointer * /*pointer*/,
                                              uint32_t /*axis*/,
                                              uint32_t /*direction*/) {
}

static const struct wl_pointer_listener pointer_listener_impl = {
    pointer_enter,
    pointer_leave,
    pointer_motion,
    pointer_button,
    pointer_axis,
    pointer_frame,
    pointer_axis_source,
    pointer_axis_stop,
    pointer_axis_discrete,
    pointer_axis_value120,
    pointer_axis_relative_direction,
};

// Seat

static void seat_capabilities(void * /*data*/, struct wl_seat *seat,
                                uint32_t caps) {
    if ((caps & WL_SEAT_CAPABILITY_KEYBOARD) && !g_keyboard) {
        g_keyboard = wl_seat_get_keyboard(seat);
        wl_keyboard_add_listener(g_keyboard, &keyboard_listener_impl, nullptr);
    }
    if ((caps & WL_SEAT_CAPABILITY_POINTER) && !g_pointer) {
        g_pointer = wl_seat_get_pointer(seat);
        wl_pointer_add_listener(g_pointer, &pointer_listener_impl, nullptr);
    }
}

static void seat_name(void * /*data*/, struct wl_seat * /*seat*/,
                        const char * /*name*/) {
}

static const struct wl_seat_listener seat_listener_impl = {
    seat_capabilities,
    seat_name,
};

// --- Entry Point ---

int main(int argc, char *argv[]) {
    // Parse command line
    if (argc < 2) {
        std::cout << "No model specified, using default scene.\n";
        CreateDefaultScene(g_state.scene);
    } else {
        std::string path = argv[1];
        std::cout << "Loading " << path << "...\n";

        if (!LoadModel(path, g_state.scene)) {
            std::cerr << "Failed to load model.\n";
            return 1;
        }
    }

    if (sceneTriangleCount(g_state.scene) == 0) {
        std::cerr << "No triangles in scene.\n";
        return 1;
    }

    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << sceneTriangleCount(g_state.scene) << " triangles.\n";

    // Initialize sun direction and accumulation buffer
    g_state.sunDirection = Vec3(1, 1, -0.5f).normalize();
    g_state.pixels.resize(g_state.width * g_state.height);
    g_state.accumBuffer.resize((size_t)g_state.width * g_state.height * 3,
                               0.0f);
    FitToScene(g_state);

    // Load Wayland + xkbcommon at runtime
    int load_result = lightrt_wayland_load(&g_wl_);
    if (load_result == -1) {
        std::cerr << "Failed to load libwayland-client.so.0 — is Wayland installed?\n";
        return 1;
    }
    if (load_result == -2) {
        std::cerr << "Failed to load libxkbcommon.so.0 — is xkbcommon installed?\n";
        lightrt_wayland_unload(&g_wl_);
        return 1;
    }

    // Create xkbcommon context
    g_xkb_ctx = xkb_context_new(XKB_CONTEXT_NO_FLAGS);
    if (!g_xkb_ctx) {
        std::cerr << "Failed to create xkb_context.\n";
        lightrt_wayland_unload(&g_wl_);
        return 1;
    }

    // Connect to Wayland display
    g_display = wl_display_connect(nullptr);
    if (!g_display) {
        std::cerr << "Cannot connect to Wayland display.\n";
        xkb_context_unref(g_xkb_ctx);
        lightrt_wayland_unload(&g_wl_);
        return 1;
    }

    // Get registry and bind globals
    struct wl_registry *registry = wl_display_get_registry(g_display);
    wl_registry_add_listener(registry, &registry_listener, nullptr);
    wl_display_roundtrip(g_display);

    if (!g_compositor || !g_shm || !g_xdg_wm_base) {
        std::cerr << "Missing required Wayland globals (compositor/shm/xdg_wm_base).\n";
        wl_display_disconnect(g_display);
        xkb_context_unref(g_xkb_ctx);
        lightrt_wayland_unload(&g_wl_);
        return 1;
    }

    // Set up xdg_wm_base listener
    xdg_wm_base_add_listener(g_xdg_wm_base, &wm_base_listener, nullptr);

    // Set up seat listener (keyboard/pointer listeners attached in callback)
    if (g_seat) {
        wl_seat_add_listener(g_seat, &seat_listener_impl, nullptr);
        wl_display_roundtrip(g_display); // Process seat capabilities
    }

    // Create surface
    g_surface = wl_compositor_create_surface(g_compositor);
    if (!g_surface) {
        std::cerr << "Failed to create wl_surface.\n";
        wl_display_disconnect(g_display);
        xkb_context_unref(g_xkb_ctx);
        lightrt_wayland_unload(&g_wl_);
        return 1;
    }

    // Create xdg_surface + xdg_toplevel
    g_xdg_surface = xdg_wm_base_get_xdg_surface(g_xdg_wm_base, g_surface);
    xdg_surface_add_listener(g_xdg_surface, &xdg_surface_listener_impl,
                              nullptr);

    g_toplevel = xdg_surface_get_toplevel(g_xdg_surface);
    xdg_toplevel_add_listener(g_toplevel, &toplevel_listener, nullptr);
    xdg_toplevel_set_title(g_toplevel, "LightRT Viewer (Wayland)");
    xdg_toplevel_set_app_id(g_toplevel, "lightrt-viewer");

    // Initial commit triggers the configure sequence
    wl_surface_commit(g_surface);

    // Wait until we get the first configure
    while (!g_configured && g_running) {
        wl_display_dispatch(g_display);
    }

    if (!g_running) {
        // Closed before configured
        xdg_toplevel_destroy(g_toplevel);
        xdg_surface_destroy(g_xdg_surface);
        wl_surface_destroy(g_surface);
        wl_display_disconnect(g_display);
        xkb_context_unref(g_xkb_ctx);
        lightrt_wayland_unload(&g_wl_);
        return 0;
    }

    // Create shared memory buffers
    if (!create_buffers(g_state.width, g_state.height)) {
        std::cerr << "Failed to create shared memory buffers.\n";
        xdg_toplevel_destroy(g_toplevel);
        xdg_surface_destroy(g_xdg_surface);
        wl_surface_destroy(g_surface);
        wl_display_disconnect(g_display);
        xkb_context_unref(g_xkb_ctx);
        lightrt_wayland_unload(&g_wl_);
        return 1;
    }

    uint64_t lastTime     = GetTimeNs();
    uint64_t fpsTimer     = lastTime;
    int      fpsFrameCount = 0;

    std::cout << "Controls: Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, "
                 "Alt+RMB/Ctrl+Shift+LMB/Tab+LMB Dolly\n";
    std::cout << "          F: Fit, S: Shadow, +: Font 2x, O: Open File (zenity/kdialog)\n";

    // Main loop
    while (g_running) {
        // Process pending Wayland events (non-blocking)
        wl_display_dispatch_pending(g_display);

        // Timing
        uint64_t now = GetTimeNs();
        float dt = (float)(now - lastTime) / 1e9f;
        lastTime = now;

        // FPS counter
        fpsFrameCount++;
        float fpsElapsed = (float)(now - fpsTimer) / 1e9f;
        if (fpsElapsed >= 1.0f) {
            g_state.fps = fpsFrameCount / fpsElapsed;
            fpsFrameCount = 0;
            fpsTimer = now;
        }

        // Process input
        if (ProcessInput(g_state, dt)) {
            g_running = false;
            break;
        }

        // Render
        RenderFrame(g_state);

        // Pick an available buffer
        int buf_idx = g_current_buffer;
        if (g_buffer_busy[buf_idx]) {
            buf_idx = 1 - buf_idx;
            if (g_buffer_busy[buf_idx]) {
                // Both busy — wait for a release event
                wl_display_dispatch(g_display);
                continue;
            }
        }
        g_current_buffer = 1 - buf_idx;

        // Copy pixels to the shared memory buffer
        size_t buf_size = (size_t)g_state.width * g_state.height * 4;
        void *dst = (char *)g_shm_data + buf_size * (size_t)buf_idx;
        memcpy(dst, g_state.pixels.data(), buf_size);

        // Attach buffer, damage, commit
        g_buffer_busy[buf_idx] = true;
        wl_surface_attach(g_surface, g_buffers[buf_idx], 0, 0);
        wl_surface_damage_buffer(g_surface, 0, 0,
                                  (int32_t)g_state.width,
                                  (int32_t)g_state.height);
        wl_surface_commit(g_surface);

        wl_display_flush(g_display);

        // Wait for events or timeout (1ms for responsive rendering)
        struct pollfd pfd;
        pfd.fd = wl_display_get_fd(g_display);
        pfd.events = POLLIN;
        poll(&pfd, 1, 1);
    }

    // Cleanup
    destroy_buffers();

    if (g_keyboard)
        wl_proxy_destroy((struct wl_proxy *)g_keyboard);
    if (g_pointer)
        wl_proxy_destroy((struct wl_proxy *)g_pointer);

    xdg_toplevel_destroy(g_toplevel);
    xdg_surface_destroy(g_xdg_surface);
    wl_surface_destroy(g_surface);

    if (g_xkb_state) xkb_state_unref(g_xkb_state);
    if (g_xkb_keymap) xkb_keymap_unref(g_xkb_keymap);
    xkb_context_unref(g_xkb_ctx);

    wl_display_disconnect(g_display);
    lightrt_wayland_unload(&g_wl_);

    return 0;
}
