/*
 * lightrt_wayland_loader.h — Runtime loader for libwayland-client.so.0
 * and libxkbcommon.so.0 via dlopen/dlsym.
 *
 * Single-header library. Define LIGHTRT_WAYLAND_IMPLEMENTATION in exactly
 * one .c/.cc file before including this header to get the implementation.
 *
 * Usage:
 *   #include "wayland/lightrt_wayland.h"
 *   #include "wayland/lightrt_xdg_shell.h"
 *   #define LIGHTRT_WAYLAND_IMPLEMENTATION
 *   #include "wayland/lightrt_wayland_loader.h"
 *
 *   // In main():
 *   if (lightrt_wayland_load(&g_wl_) != 0) { error; }
 *   // ... use Wayland calls normally (redirected via macros) ...
 *   lightrt_wayland_unload(&g_wl_);
 */

#ifndef LIGHTRT_WAYLAND_LOADER_H
#define LIGHTRT_WAYLAND_LOADER_H

#include "lightrt_wayland.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ================================================================
 * Function pointer table
 * ================================================================ */

typedef struct LightrtWayland {
    void *wl_handle;   /* libwayland-client.so.0 */
    void *xkb_handle;  /* libxkbcommon.so.0 */

    /* Display */
    struct wl_display* (*wl_display_connect)(const char *);
    void (*wl_display_disconnect)(struct wl_display *);
    int (*wl_display_dispatch)(struct wl_display *);
    int (*wl_display_dispatch_pending)(struct wl_display *);
    int (*wl_display_roundtrip)(struct wl_display *);
    int (*wl_display_flush)(struct wl_display *);
    int (*wl_display_get_fd)(struct wl_display *);

    /* Proxy */
    struct wl_proxy* (*wl_proxy_marshal_flags)(struct wl_proxy *, uint32_t,
        const struct wl_interface *, uint32_t, uint32_t, ...);
    int (*wl_proxy_add_listener)(struct wl_proxy *,
        void (**)(void), void *);
    uint32_t (*wl_proxy_get_version)(struct wl_proxy *);
    void (*wl_proxy_destroy)(struct wl_proxy *);

    /* Core interface variables (pointers to const wl_interface) */
    const struct wl_interface *wl_registry_interface;
    const struct wl_interface *wl_compositor_interface;
    const struct wl_interface *wl_surface_interface;
    const struct wl_interface *wl_shm_interface;
    const struct wl_interface *wl_shm_pool_interface;
    const struct wl_interface *wl_buffer_interface;
    const struct wl_interface *wl_callback_interface;
    const struct wl_interface *wl_seat_interface;
    const struct wl_interface *wl_keyboard_interface;
    const struct wl_interface *wl_pointer_interface;
    const struct wl_interface *wl_output_interface;
    const struct wl_interface *wl_region_interface;

    /* xkbcommon */
    struct xkb_context* (*xkb_context_new)(enum xkb_context_flags);
    void (*xkb_context_unref)(struct xkb_context *);
    struct xkb_keymap* (*xkb_keymap_new_from_string)(struct xkb_context *,
        const char *, enum xkb_keymap_format, enum xkb_keymap_compile_flags);
    void (*xkb_keymap_unref)(struct xkb_keymap *);
    struct xkb_state* (*xkb_state_new)(struct xkb_keymap *);
    void (*xkb_state_unref)(struct xkb_state *);
    uint32_t (*xkb_state_key_get_one_sym)(struct xkb_state *, uint32_t);
    int (*xkb_state_update_mask)(struct xkb_state *, uint32_t, uint32_t,
        uint32_t, uint32_t, uint32_t, uint32_t);
} LightrtWayland;

/* Global instance used by macro redirects below */
static LightrtWayland g_wl_;

/* Loader API */
static int  lightrt_wayland_load(LightrtWayland *wl);
static void lightrt_wayland_unload(LightrtWayland *wl);

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_WAYLAND_LOADER_H */

/* ================================================================
 * Implementation — compiled when LIGHTRT_WAYLAND_IMPLEMENTATION
 * is defined. MUST appear before the macro redirects so the raw
 * member names are visible inside lightrt_wayland_load().
 * ================================================================ */

#ifdef LIGHTRT_WAYLAND_IMPLEMENTATION
#undef LIGHTRT_WAYLAND_IMPLEMENTATION

#include "lightrt_xdg_shell.h"

/* Pull in xdg_shell implementation here */
#define LIGHTRT_XDG_SHELL_IMPLEMENTATION
#include "lightrt_xdg_shell.h"

#include <dlfcn.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Helper macro — load one function symbol, fail if missing */
#define LIGHTRT_WL_LOAD_SYM(wl, name)                                   \
    do {                                                                 \
        *((void **)&(wl)->name) = dlsym((wl)->wl_handle, #name);        \
        if (!(wl)->name) return -1;                                      \
    } while (0)

/* Helper macro — load one interface variable (pointer to struct wl_interface) */
#define LIGHTRT_WL_LOAD_IFACE(wl, name)                                  \
    do {                                                                  \
        (wl)->name = (const struct wl_interface *)dlsym((wl)->wl_handle, #name); \
        if (!(wl)->name) return -1;                                       \
    } while (0)

/* Helper macro — load one xkbcommon function symbol */
#define LIGHTRT_XKB_LOAD_SYM(wl, name)                                   \
    do {                                                                  \
        *((void **)&(wl)->name) = dlsym((wl)->xkb_handle, #name);        \
        if (!(wl)->name) return -1;                                       \
    } while (0)

static int lightrt_wayland_load(LightrtWayland *wl) {
    memset(wl, 0, sizeof(*wl));

    /* Load libwayland-client */
    wl->wl_handle = dlopen("libwayland-client.so.0", RTLD_LAZY);
    if (!wl->wl_handle)
        wl->wl_handle = dlopen("libwayland-client.so", RTLD_LAZY);
    if (!wl->wl_handle)
        return -1;

    /* Display functions */
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_connect);
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_disconnect);
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_dispatch);
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_dispatch_pending);
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_roundtrip);
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_flush);
    LIGHTRT_WL_LOAD_SYM(wl, wl_display_get_fd);

    /* Proxy functions */
    LIGHTRT_WL_LOAD_SYM(wl, wl_proxy_marshal_flags);
    LIGHTRT_WL_LOAD_SYM(wl, wl_proxy_add_listener);
    LIGHTRT_WL_LOAD_SYM(wl, wl_proxy_get_version);
    LIGHTRT_WL_LOAD_SYM(wl, wl_proxy_destroy);

    /* Core interface variables */
    LIGHTRT_WL_LOAD_IFACE(wl, wl_registry_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_compositor_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_surface_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_shm_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_shm_pool_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_buffer_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_callback_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_seat_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_keyboard_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_pointer_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_output_interface);
    LIGHTRT_WL_LOAD_IFACE(wl, wl_region_interface);

    /* Load libxkbcommon */
    wl->xkb_handle = dlopen("libxkbcommon.so.0", RTLD_LAZY);
    if (!wl->xkb_handle)
        wl->xkb_handle = dlopen("libxkbcommon.so", RTLD_LAZY);
    if (!wl->xkb_handle)
        return -2;

    /* xkbcommon functions */
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_context_new);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_context_unref);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_keymap_new_from_string);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_keymap_unref);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_state_new);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_state_unref);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_state_key_get_one_sym);
    LIGHTRT_XKB_LOAD_SYM(wl, xkb_state_update_mask);

    /* Initialize XDG shell type arrays with loaded interfaces */
    lightrt_xdg_shell_init(wl->wl_surface_interface,
                           wl->wl_seat_interface,
                           wl->wl_output_interface);

    return 0;
}

#undef LIGHTRT_WL_LOAD_SYM
#undef LIGHTRT_WL_LOAD_IFACE
#undef LIGHTRT_XKB_LOAD_SYM

static void lightrt_wayland_unload(LightrtWayland *wl) {
    if (wl->xkb_handle) {
        dlclose(wl->xkb_handle);
        wl->xkb_handle = 0;
    }
    if (wl->wl_handle) {
        dlclose(wl->wl_handle);
        wl->wl_handle = 0;
    }
}

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_WAYLAND_IMPLEMENTATION */

/* ================================================================
 * Macro redirects — make Wayland/xkbcommon calls go through the loader.
 * These MUST come after the implementation section so that
 * lightrt_wayland_load() sees the raw struct member names.
 * ================================================================ */

#ifndef LIGHTRT_WL_MACROS_DEFINED_
#define LIGHTRT_WL_MACROS_DEFINED_

/* Display functions */
#define wl_display_connect        g_wl_.wl_display_connect
#define wl_display_disconnect     g_wl_.wl_display_disconnect
#define wl_display_dispatch       g_wl_.wl_display_dispatch
#define wl_display_dispatch_pending g_wl_.wl_display_dispatch_pending
#define wl_display_roundtrip      g_wl_.wl_display_roundtrip
#define wl_display_flush          g_wl_.wl_display_flush
#define wl_display_get_fd         g_wl_.wl_display_get_fd

/* Proxy functions */
#define wl_proxy_marshal_flags    g_wl_.wl_proxy_marshal_flags
#define wl_proxy_add_listener     g_wl_.wl_proxy_add_listener
#define wl_proxy_get_version      g_wl_.wl_proxy_get_version
#define wl_proxy_destroy          g_wl_.wl_proxy_destroy

/* Interface variable redirects — dereference pointer so &name works */
#define wl_registry_interface     (*g_wl_.wl_registry_interface)
#define wl_compositor_interface   (*g_wl_.wl_compositor_interface)
#define wl_surface_interface      (*g_wl_.wl_surface_interface)
#define wl_shm_interface          (*g_wl_.wl_shm_interface)
#define wl_shm_pool_interface     (*g_wl_.wl_shm_pool_interface)
#define wl_buffer_interface       (*g_wl_.wl_buffer_interface)
#define wl_callback_interface     (*g_wl_.wl_callback_interface)
#define wl_seat_interface         (*g_wl_.wl_seat_interface)
#define wl_keyboard_interface     (*g_wl_.wl_keyboard_interface)
#define wl_pointer_interface      (*g_wl_.wl_pointer_interface)
#define wl_output_interface       (*g_wl_.wl_output_interface)
#define wl_region_interface       (*g_wl_.wl_region_interface)

/* xkbcommon functions */
#define xkb_context_new           g_wl_.xkb_context_new
#define xkb_context_unref         g_wl_.xkb_context_unref
#define xkb_keymap_new_from_string g_wl_.xkb_keymap_new_from_string
#define xkb_keymap_unref          g_wl_.xkb_keymap_unref
#define xkb_state_new             g_wl_.xkb_state_new
#define xkb_state_unref           g_wl_.xkb_state_unref
#define xkb_state_key_get_one_sym g_wl_.xkb_state_key_get_one_sym
#define xkb_state_update_mask     g_wl_.xkb_state_update_mask

/* ================================================================
 * Inline wrapper functions for Wayland protocol requests.
 * These call wl_proxy_marshal_flags through the loader macros above.
 * ================================================================ */

/* --- wl_display --- */

static inline struct wl_registry *
wl_display_get_registry(struct wl_display *display) {
    return (struct wl_registry *)
        wl_proxy_marshal_flags((struct wl_proxy *)display,
            WL_DISPLAY_GET_REGISTRY, &wl_registry_interface,
            wl_proxy_get_version((struct wl_proxy *)display), 0, NULL);
}

static inline struct wl_callback *
wl_display_sync(struct wl_display *display) {
    return (struct wl_callback *)
        wl_proxy_marshal_flags((struct wl_proxy *)display,
            WL_DISPLAY_SYNC, &wl_callback_interface,
            wl_proxy_get_version((struct wl_proxy *)display), 0, NULL);
}

/* --- wl_registry --- */

static inline int
wl_registry_add_listener(struct wl_registry *registry,
                          const struct wl_registry_listener *listener,
                          void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)registry,
        (void (**)(void))listener, data);
}

static inline void *
wl_registry_bind(struct wl_registry *registry, uint32_t name,
                  const struct wl_interface *interface, uint32_t version) {
    return (void *)
        wl_proxy_marshal_flags((struct wl_proxy *)registry,
            WL_REGISTRY_BIND, interface, version, 0,
            name, interface->name, version, NULL);
}

/* --- wl_compositor --- */

static inline struct wl_surface *
wl_compositor_create_surface(struct wl_compositor *compositor) {
    return (struct wl_surface *)
        wl_proxy_marshal_flags((struct wl_proxy *)compositor,
            WL_COMPOSITOR_CREATE_SURFACE, &wl_surface_interface,
            wl_proxy_get_version((struct wl_proxy *)compositor), 0, NULL);
}

/* --- wl_surface --- */

static inline void
wl_surface_attach(struct wl_surface *surface, struct wl_buffer *buffer,
                   int32_t x, int32_t y) {
    wl_proxy_marshal_flags((struct wl_proxy *)surface,
        WL_SURFACE_ATTACH, NULL,
        wl_proxy_get_version((struct wl_proxy *)surface), 0,
        buffer, x, y);
}

static inline void
wl_surface_damage_buffer(struct wl_surface *surface,
                          int32_t x, int32_t y,
                          int32_t width, int32_t height) {
    wl_proxy_marshal_flags((struct wl_proxy *)surface,
        WL_SURFACE_DAMAGE_BUFFER, NULL,
        wl_proxy_get_version((struct wl_proxy *)surface), 0,
        x, y, width, height);
}

static inline struct wl_callback *
wl_surface_frame(struct wl_surface *surface) {
    return (struct wl_callback *)
        wl_proxy_marshal_flags((struct wl_proxy *)surface,
            WL_SURFACE_FRAME, &wl_callback_interface,
            wl_proxy_get_version((struct wl_proxy *)surface), 0, NULL);
}

static inline void
wl_surface_commit(struct wl_surface *surface) {
    wl_proxy_marshal_flags((struct wl_proxy *)surface,
        WL_SURFACE_COMMIT, NULL,
        wl_proxy_get_version((struct wl_proxy *)surface), 0);
}

static inline void
wl_surface_destroy(struct wl_surface *surface) {
    wl_proxy_marshal_flags((struct wl_proxy *)surface,
        WL_SURFACE_DESTROY, NULL,
        wl_proxy_get_version((struct wl_proxy *)surface),
        WL_MARSHAL_FLAG_DESTROY);
}

/* --- wl_shm --- */

static inline int
wl_shm_add_listener(struct wl_shm *shm,
                      const struct wl_shm_listener *listener, void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)shm,
        (void (**)(void))listener, data);
}

static inline struct wl_shm_pool *
wl_shm_create_pool(struct wl_shm *shm, int32_t fd, int32_t size) {
    return (struct wl_shm_pool *)
        wl_proxy_marshal_flags((struct wl_proxy *)shm,
            WL_SHM_CREATE_POOL, &wl_shm_pool_interface,
            wl_proxy_get_version((struct wl_proxy *)shm), 0,
            NULL, fd, size);
}

/* --- wl_shm_pool --- */

static inline struct wl_buffer *
wl_shm_pool_create_buffer(struct wl_shm_pool *pool,
                            int32_t offset, int32_t width, int32_t height,
                            int32_t stride, uint32_t format) {
    return (struct wl_buffer *)
        wl_proxy_marshal_flags((struct wl_proxy *)pool,
            WL_SHM_POOL_CREATE_BUFFER, &wl_buffer_interface,
            wl_proxy_get_version((struct wl_proxy *)pool), 0,
            NULL, offset, width, height, stride, format);
}

static inline void
wl_shm_pool_destroy(struct wl_shm_pool *pool) {
    wl_proxy_marshal_flags((struct wl_proxy *)pool,
        WL_SHM_POOL_DESTROY, NULL,
        wl_proxy_get_version((struct wl_proxy *)pool),
        WL_MARSHAL_FLAG_DESTROY);
}

/* --- wl_buffer --- */

static inline int
wl_buffer_add_listener(struct wl_buffer *buffer,
                        const struct wl_buffer_listener *listener,
                        void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)buffer,
        (void (**)(void))listener, data);
}

static inline void
wl_buffer_destroy(struct wl_buffer *buffer) {
    wl_proxy_marshal_flags((struct wl_proxy *)buffer,
        WL_BUFFER_DESTROY, NULL,
        wl_proxy_get_version((struct wl_proxy *)buffer),
        WL_MARSHAL_FLAG_DESTROY);
}

/* --- wl_callback --- */

static inline int
wl_callback_add_listener(struct wl_callback *callback,
                          const struct wl_callback_listener *listener,
                          void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)callback,
        (void (**)(void))listener, data);
}

/* --- wl_seat --- */

static inline int
wl_seat_add_listener(struct wl_seat *seat,
                      const struct wl_seat_listener *listener, void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)seat,
        (void (**)(void))listener, data);
}

static inline struct wl_pointer *
wl_seat_get_pointer(struct wl_seat *seat) {
    return (struct wl_pointer *)
        wl_proxy_marshal_flags((struct wl_proxy *)seat,
            WL_SEAT_GET_POINTER, &wl_pointer_interface,
            wl_proxy_get_version((struct wl_proxy *)seat), 0, NULL);
}

static inline struct wl_keyboard *
wl_seat_get_keyboard(struct wl_seat *seat) {
    return (struct wl_keyboard *)
        wl_proxy_marshal_flags((struct wl_proxy *)seat,
            WL_SEAT_GET_KEYBOARD, &wl_keyboard_interface,
            wl_proxy_get_version((struct wl_proxy *)seat), 0, NULL);
}

/* --- wl_keyboard --- */

static inline int
wl_keyboard_add_listener(struct wl_keyboard *keyboard,
                          const struct wl_keyboard_listener *listener,
                          void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)keyboard,
        (void (**)(void))listener, data);
}

/* --- wl_pointer --- */

static inline int
wl_pointer_add_listener(struct wl_pointer *pointer,
                         const struct wl_pointer_listener *listener,
                         void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)pointer,
        (void (**)(void))listener, data);
}

/* --- xdg_wm_base --- */

static inline int
xdg_wm_base_add_listener(struct xdg_wm_base *wm_base,
                           const struct xdg_wm_base_listener *listener,
                           void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)wm_base,
        (void (**)(void))listener, data);
}

static inline void
xdg_wm_base_pong(struct xdg_wm_base *wm_base, uint32_t serial) {
    wl_proxy_marshal_flags((struct wl_proxy *)wm_base,
        XDG_WM_BASE_PONG, NULL,
        wl_proxy_get_version((struct wl_proxy *)wm_base), 0,
        serial);
}

static inline struct xdg_surface *
xdg_wm_base_get_xdg_surface(struct xdg_wm_base *wm_base,
                              struct wl_surface *surface) {
    return (struct xdg_surface *)
        wl_proxy_marshal_flags((struct wl_proxy *)wm_base,
            XDG_WM_BASE_GET_XDG_SURFACE, &xdg_surface_interface,
            wl_proxy_get_version((struct wl_proxy *)wm_base), 0,
            NULL, surface);
}

static inline void
xdg_wm_base_destroy(struct xdg_wm_base *wm_base) {
    wl_proxy_marshal_flags((struct wl_proxy *)wm_base,
        XDG_WM_BASE_DESTROY, NULL,
        wl_proxy_get_version((struct wl_proxy *)wm_base),
        WL_MARSHAL_FLAG_DESTROY);
}

/* --- xdg_surface --- */

static inline int
xdg_surface_add_listener(struct xdg_surface *xdg_surface,
                           const struct xdg_surface_listener *listener,
                           void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)xdg_surface,
        (void (**)(void))listener, data);
}

static inline struct xdg_toplevel *
xdg_surface_get_toplevel(struct xdg_surface *xdg_surface) {
    return (struct xdg_toplevel *)
        wl_proxy_marshal_flags((struct wl_proxy *)xdg_surface,
            XDG_SURFACE_GET_TOPLEVEL, &xdg_toplevel_interface,
            wl_proxy_get_version((struct wl_proxy *)xdg_surface), 0, NULL);
}

static inline void
xdg_surface_ack_configure(struct xdg_surface *xdg_surface, uint32_t serial) {
    wl_proxy_marshal_flags((struct wl_proxy *)xdg_surface,
        XDG_SURFACE_ACK_CONFIGURE, NULL,
        wl_proxy_get_version((struct wl_proxy *)xdg_surface), 0,
        serial);
}

static inline void
xdg_surface_destroy(struct xdg_surface *xdg_surface) {
    wl_proxy_marshal_flags((struct wl_proxy *)xdg_surface,
        XDG_SURFACE_DESTROY, NULL,
        wl_proxy_get_version((struct wl_proxy *)xdg_surface),
        WL_MARSHAL_FLAG_DESTROY);
}

/* --- xdg_toplevel --- */

static inline int
xdg_toplevel_add_listener(struct xdg_toplevel *toplevel,
                            const struct xdg_toplevel_listener *listener,
                            void *data) {
    return wl_proxy_add_listener((struct wl_proxy *)toplevel,
        (void (**)(void))listener, data);
}

static inline void
xdg_toplevel_set_title(struct xdg_toplevel *toplevel, const char *title) {
    wl_proxy_marshal_flags((struct wl_proxy *)toplevel,
        XDG_TOPLEVEL_SET_TITLE, NULL,
        wl_proxy_get_version((struct wl_proxy *)toplevel), 0,
        title);
}

static inline void
xdg_toplevel_set_app_id(struct xdg_toplevel *toplevel, const char *app_id) {
    wl_proxy_marshal_flags((struct wl_proxy *)toplevel,
        XDG_TOPLEVEL_SET_APP_ID, NULL,
        wl_proxy_get_version((struct wl_proxy *)toplevel), 0,
        app_id);
}

static inline void
xdg_toplevel_destroy(struct xdg_toplevel *toplevel) {
    wl_proxy_marshal_flags((struct wl_proxy *)toplevel,
        XDG_TOPLEVEL_DESTROY, NULL,
        wl_proxy_get_version((struct wl_proxy *)toplevel),
        WL_MARSHAL_FLAG_DESTROY);
}

#endif /* LIGHTRT_WL_MACROS_DEFINED_ */
