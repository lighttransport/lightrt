// Pure X11 viewer — no GLFW, no Vulkan, no external deps beyond lightrt + X11
// X11 loaded at runtime via dlopen — no libx11-dev needed at compile time.

#include "x11/lightrt_x11.h"
#define LIGHTRT_X11_IMPLEMENTATION
#include "x11/lightrt_x11_loader.h"

#include "common/viewer_common.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <time.h>

using namespace lightrt_viewer;

// --- Globals ---
static ViewerState g_state;
static bool        g_running = true;

// --- Timing helpers ---

static uint64_t GetTimeNs() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

// --- Entry Point ---

int main(int argc, char* argv[]) {
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

    g_state.scene.build();

    if (g_state.scene.allTriangles.empty()) {
        std::cerr << "No triangles in scene.\n";
        return 1;
    }

    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << g_state.scene.allTriangles.size() << " triangles.\n";

    // Initialize sun direction and accumulation buffer
    g_state.sunDirection = Vec3(1, 1, -0.5f).normalize();
    g_state.pixels.resize(g_state.width * g_state.height);
    g_state.accumBuffer.resize((size_t)g_state.width * g_state.height * 3, 0.0f);
    FitToScene(g_state);

    // Load X11 at runtime
    if (lightrt_x11_load(&g_x11_) != 0) {
        std::cerr << "Failed to load libX11.so.6 — is X11 installed?\n";
        return 1;
    }

    // Open X11 display
    Display* dpy = XOpenDisplay(nullptr);
    if (!dpy) {
        std::cerr << "Cannot open X display.\n";
        lightrt_x11_unload(&g_x11_);
        return 1;
    }

    int screen = DefaultScreen(dpy);
    Window root = RootWindow(dpy, screen);
    Visual* visual = DefaultVisual(dpy, screen);
    int depth = DefaultDepth(dpy, screen);

    // Require 24/32-bit TrueColor for direct pixel blitting
    if (depth < 24) {
        std::cerr << "Need 24-bit or 32-bit display depth, got " << depth << ".\n";
        XCloseDisplay(dpy);
        return 1;
    }

    // Create window
    XSetWindowAttributes attrs;
    attrs.background_pixel = BlackPixel(dpy, screen);
    attrs.event_mask = ExposureMask | StructureNotifyMask |
                       KeyPressMask | KeyReleaseMask |
                       ButtonPressMask | ButtonReleaseMask |
                       PointerMotionMask;

    Window win = XCreateWindow(
        dpy, root,
        0, 0, g_state.width, g_state.height,
        0, depth, InputOutput, visual,
        CWBackPixel | CWEventMask, &attrs);

    XStoreName(dpy, win, "LightRT Viewer (X11)");

    // Handle WM_DELETE_WINDOW
    Atom wm_delete = XInternAtom(dpy, "WM_DELETE_WINDOW", False);
    XSetWMProtocols(dpy, win, &wm_delete, 1);

    XMapWindow(dpy, win);

    // Create GC for drawing
    GC gc = XCreateGC(dpy, win, 0, nullptr);

    // Create XImage for pixel blitting
    XImage* ximg = XCreateImage(
        dpy, visual, depth, ZPixmap, 0,
        (char*)g_state.pixels.data(),
        g_state.width, g_state.height,
        32, 0);
    // XImage does NOT own the pixel data — we manage it
    ximg->byte_order = LSBFirst;

    uint64_t lastTime = GetTimeNs();
    uint64_t fpsTimer = lastTime;
    int fpsFrameCount = 0;

    std::cout << "Controls: Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, Alt+RMB/Ctrl+Shift+LMB/Tab+LMB Dolly\n";
    std::cout << "          F: Fit, S: Shadow, O: Font 2x\n";

    // Main loop
    while (g_running) {
        // Process all pending events
        while (XPending(dpy)) {
            XEvent ev;
            XNextEvent(dpy, &ev);

            switch (ev.type) {
            case ClientMessage:
                if ((Atom)ev.xclient.data.l[0] == wm_delete) {
                    g_running = false;
                }
                break;

            case ConfigureNotify: {
                uint32_t w = (uint32_t)ev.xconfigure.width;
                uint32_t h = (uint32_t)ev.xconfigure.height;
                if (w > 0 && h > 0 && (w != g_state.width || h != g_state.height)) {
                    ResizeFramebuffer(g_state, w, h);

                    // Recreate XImage for new size
                    // Set data to null so XDestroyImage doesn't free our buffer
                    ximg->data = nullptr;
                    XDestroyImage(ximg);

                    ximg = XCreateImage(
                        dpy, visual, depth, ZPixmap, 0,
                        (char*)g_state.pixels.data(),
                        g_state.width, g_state.height,
                        32, 0);
                    ximg->byte_order = LSBFirst;
                }
                break;
            }

            case KeyPress: {
                KeySym ks = XLookupKeysym(&ev.xkey, 0);
                switch (ks) {
                case XK_f: case XK_F:
                    g_state.keys[KEY_F] = true; break;
                case XK_s: case XK_S:
                    g_state.keys[KEY_S] = true; break;
                case XK_o: case XK_O:
                    g_state.keys[KEY_O] = true; break;
                case XK_Escape:
                    g_state.keys[KEY_ESCAPE] = true; break;
                case XK_Shift_L: case XK_Shift_R:
                    g_state.shiftPressed = true; break;
                case XK_Control_L: case XK_Control_R:
                    g_state.ctrlPressed = true; break;
                case XK_Alt_L: case XK_Alt_R:
                    g_state.altPressed = true; break;
                case XK_Tab:
                    g_state.tabPressed = true; break;
                }
                break;
            }

            case KeyRelease: {
                // Filter out auto-repeat: if next event is KeyPress of same key, skip both
                if (XEventsQueued(dpy, QueuedAfterReading)) {
                    XEvent next;
                    XPeekEvent(dpy, &next);
                    if (next.type == KeyPress &&
                        next.xkey.time == ev.xkey.time &&
                        next.xkey.keycode == ev.xkey.keycode) {
                        // Auto-repeat pair — consume the KeyPress and ignore both
                        XNextEvent(dpy, &next);
                        break;
                    }
                }

                KeySym ks = XLookupKeysym(&ev.xkey, 0);
                switch (ks) {
                case XK_f: case XK_F:
                    g_state.keys[KEY_F] = false; break;
                case XK_s: case XK_S:
                    g_state.keys[KEY_S] = false; break;
                case XK_o: case XK_O:
                    g_state.keys[KEY_O] = false; break;
                case XK_Escape:
                    g_state.keys[KEY_ESCAPE] = false; break;
                case XK_Shift_L: case XK_Shift_R:
                    g_state.shiftPressed = false; break;
                case XK_Control_L: case XK_Control_R:
                    g_state.ctrlPressed = false; break;
                case XK_Alt_L: case XK_Alt_R:
                    g_state.altPressed = false; break;
                case XK_Tab:
                    g_state.tabPressed = false; break;
                }
                break;
            }

            case ButtonPress: {
                double x = (double)ev.xbutton.x;
                double y = (double)ev.xbutton.y;
                switch (ev.xbutton.button) {
                case Button1:
                    g_state.lmbPressed = true;
                    OnMouseDown(g_state, x, y);
                    break;
                case Button2:
                    g_state.mmbPressed = true;
                    OnMouseDown(g_state, x, y);
                    break;
                case Button3:
                    g_state.rmbPressed = true;
                    OnMouseDown(g_state, x, y);
                    break;
                case Button4: // Scroll up
                    DollyCamera(g_state, -0.3f);
                    break;
                case Button5: // Scroll down
                    DollyCamera(g_state, 0.3f);
                    break;
                }
                break;
            }

            case ButtonRelease: {
                switch (ev.xbutton.button) {
                case Button1:
                    g_state.lmbPressed = false;
                    if (!g_state.mmbPressed && !g_state.rmbPressed)
                        g_state.dragging = false;
                    break;
                case Button2:
                    g_state.mmbPressed = false;
                    if (!g_state.lmbPressed && !g_state.rmbPressed)
                        g_state.dragging = false;
                    break;
                case Button3:
                    g_state.rmbPressed = false;
                    if (!g_state.lmbPressed && !g_state.mmbPressed)
                        g_state.dragging = false;
                    break;
                }
                break;
            }

            case MotionNotify: {
                double x = (double)ev.xmotion.x;
                double y = (double)ev.xmotion.y;
                OnMouseDrag(g_state, x, y);
                break;
            }
            } // switch
        } // while XPending

        if (!g_running) break;

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

        // Blit to window via XPutImage
        // g_state.pixels is BGRA (uint32_t) which matches X11 ZPixmap on little-endian
        XPutImage(dpy, win, gc, ximg,
                  0, 0, 0, 0, g_state.width, g_state.height);
        XFlush(dpy);
    }

    // Cleanup — set data to null so XDestroyImage doesn't free our buffer
    ximg->data = nullptr;
    XDestroyImage(ximg);
    XFreeGC(dpy, gc);
    XDestroyWindow(dpy, win);
    XCloseDisplay(dpy);
    lightrt_x11_unload(&g_x11_);

    return 0;
}
