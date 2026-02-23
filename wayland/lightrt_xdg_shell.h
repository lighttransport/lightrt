/*
 * lightrt_xdg_shell.h — XDG shell protocol interfaces for LightRT viewer.
 *
 * Hand-written from xdg-shell.xml (stable protocol, version 6).
 * Provides the same ABI as wayland-scanner-generated code without
 * requiring wayland-protocols or wayland-scanner at build time.
 *
 * Call lightrt_xdg_shell_init() after loading libwayland-client to
 * fill in core interface references in the type arrays.
 */

#ifndef LIGHTRT_XDG_SHELL_H
#define LIGHTRT_XDG_SHELL_H

#include "lightrt_wayland.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ================================================================
 * Opaque XDG shell types
 * ================================================================ */

struct xdg_wm_base;
struct xdg_surface;
struct xdg_toplevel;
struct xdg_positioner;
struct xdg_popup;

/* ================================================================
 * XDG shell opcodes
 * ================================================================ */

/* xdg_wm_base requests */
#define XDG_WM_BASE_DESTROY                 0
#define XDG_WM_BASE_CREATE_POSITIONER       1
#define XDG_WM_BASE_GET_XDG_SURFACE         2
#define XDG_WM_BASE_PONG                    3

/* xdg_surface requests */
#define XDG_SURFACE_DESTROY                 0
#define XDG_SURFACE_GET_TOPLEVEL            1
#define XDG_SURFACE_GET_POPUP               2
#define XDG_SURFACE_SET_WINDOW_GEOMETRY     3
#define XDG_SURFACE_ACK_CONFIGURE           4

/* xdg_toplevel requests */
#define XDG_TOPLEVEL_DESTROY                0
#define XDG_TOPLEVEL_SET_PARENT             1
#define XDG_TOPLEVEL_SET_TITLE              2
#define XDG_TOPLEVEL_SET_APP_ID             3
#define XDG_TOPLEVEL_SHOW_WINDOW_MENU       4
#define XDG_TOPLEVEL_MOVE                   5
#define XDG_TOPLEVEL_RESIZE                 6
#define XDG_TOPLEVEL_SET_MAX_SIZE           7
#define XDG_TOPLEVEL_SET_MIN_SIZE           8
#define XDG_TOPLEVEL_SET_MAXIMIZED          9
#define XDG_TOPLEVEL_UNSET_MAXIMIZED        10
#define XDG_TOPLEVEL_SET_FULLSCREEN         11
#define XDG_TOPLEVEL_UNSET_FULLSCREEN       12
#define XDG_TOPLEVEL_SET_MINIMIZED          13

/* ================================================================
 * Listener structs
 * ================================================================ */

struct xdg_wm_base_listener {
    void (*ping)(void *data, struct xdg_wm_base *xdg_wm_base,
                 uint32_t serial);
};

struct xdg_surface_listener {
    void (*configure)(void *data, struct xdg_surface *xdg_surface,
                      uint32_t serial);
};

struct xdg_toplevel_listener {
    void (*configure)(void *data, struct xdg_toplevel *xdg_toplevel,
                      int32_t width, int32_t height,
                      struct wl_array *states);
    void (*close)(void *data, struct xdg_toplevel *xdg_toplevel);
    void (*configure_bounds)(void *data, struct xdg_toplevel *xdg_toplevel,
                             int32_t width, int32_t height);
    void (*wm_capabilities)(void *data, struct xdg_toplevel *xdg_toplevel,
                            struct wl_array *capabilities);
};

/* ================================================================
 * Interface declarations (extern — defined in implementation)
 * ================================================================ */

extern struct wl_interface xdg_wm_base_interface;
extern struct wl_interface xdg_surface_interface;
extern struct wl_interface xdg_toplevel_interface;
extern struct wl_interface xdg_positioner_interface;
extern struct wl_interface xdg_popup_interface;

/* ================================================================
 * Init function — must be called after loading libwayland-client
 * Fills in mutable type arrays with core Wayland interface pointers.
 * ================================================================ */

void lightrt_xdg_shell_init(const struct wl_interface *wl_surface_iface,
                             const struct wl_interface *wl_seat_iface,
                             const struct wl_interface *wl_output_iface);

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_XDG_SHELL_H */

/* ================================================================
 * Implementation — compiled when LIGHTRT_XDG_SHELL_IMPLEMENTATION
 * is defined in exactly one translation unit.
 * ================================================================ */

#ifdef LIGHTRT_XDG_SHELL_IMPLEMENTATION
#undef LIGHTRT_XDG_SHELL_IMPLEMENTATION

#ifdef __cplusplus
extern "C" {
#endif

/* ----------------------------------------------------------------
 * Mutable type arrays for message structs.
 * These reference core Wayland interfaces (wl_surface, wl_seat, etc.)
 * which are only available after dlopen. lightrt_xdg_shell_init()
 * fills them in.
 * ---------------------------------------------------------------- */

/* xdg_wm_base types */
static const struct wl_interface *xdg_wm_base_request_types[4] = {
    NULL,  /* destroy: no types */
    NULL,  /* create_positioner: xdg_positioner (filled by init) */
    NULL,  /* get_xdg_surface [0]: xdg_surface (filled by init) */
    NULL,  /* get_xdg_surface [1]: wl_surface (filled by init) */
};

/* xdg_surface types */
static const struct wl_interface *xdg_surface_request_types[6] = {
    NULL,  /* destroy: no types */
    NULL,  /* get_toplevel: xdg_toplevel (filled by init) */
    NULL,  /* get_popup [0]: xdg_popup (filled by init) */
    NULL,  /* get_popup [1]: xdg_surface (filled by init, nullable) */
    NULL,  /* get_popup [2]: xdg_positioner (filled by init) */
    NULL,  /* set_window_geometry / ack_configure: no types */
};

/* xdg_toplevel types */
static const struct wl_interface *xdg_toplevel_request_types[5] = {
    NULL,  /* destroy: no types */
    NULL,  /* set_parent: xdg_toplevel (filled by init, nullable) */
    NULL,  /* show_window_menu: wl_seat (filled by init) */
    NULL,  /* move: wl_seat (filled by init) */
    NULL,  /* resize: wl_seat (filled by init) */
};

/* xdg_toplevel set_fullscreen type */
static const struct wl_interface *xdg_toplevel_fullscreen_types[1] = {
    NULL,  /* set_fullscreen: wl_output (filled by init, nullable) */
};

/* ----------------------------------------------------------------
 * xdg_wm_base interface
 * ---------------------------------------------------------------- */

static const struct wl_message xdg_wm_base_requests[] = {
    { "destroy",            "",   xdg_wm_base_request_types + 0 },
    { "create_positioner",  "n",  xdg_wm_base_request_types + 1 },
    { "get_xdg_surface",    "no", xdg_wm_base_request_types + 2 },
    { "pong",               "u",  xdg_wm_base_request_types + 0 },
};

static const struct wl_message xdg_wm_base_events[] = {
    { "ping", "u", xdg_wm_base_request_types + 0 },
};

struct wl_interface xdg_wm_base_interface = {
    "xdg_wm_base", 6,
    4, xdg_wm_base_requests,
    1, xdg_wm_base_events,
};

/* ----------------------------------------------------------------
 * xdg_positioner interface (stub — never instantiated by viewer)
 * ---------------------------------------------------------------- */

struct wl_interface xdg_positioner_interface = {
    "xdg_positioner", 6,
    0, NULL,
    0, NULL,
};

/* ----------------------------------------------------------------
 * xdg_surface interface
 * ---------------------------------------------------------------- */

static const struct wl_message xdg_surface_requests[] = {
    { "destroy",              "",     xdg_surface_request_types + 0 },
    { "get_toplevel",         "n",    xdg_surface_request_types + 1 },
    { "get_popup",            "n?oo", xdg_surface_request_types + 2 },
    { "set_window_geometry",  "iiii", xdg_surface_request_types + 0 },
    { "ack_configure",        "u",    xdg_surface_request_types + 0 },
};

static const struct wl_message xdg_surface_events[] = {
    { "configure", "u", xdg_surface_request_types + 0 },
};

struct wl_interface xdg_surface_interface = {
    "xdg_surface", 6,
    5, xdg_surface_requests,
    1, xdg_surface_events,
};

/* ----------------------------------------------------------------
 * xdg_popup interface (stub — never instantiated by viewer)
 * ---------------------------------------------------------------- */

struct wl_interface xdg_popup_interface = {
    "xdg_popup", 6,
    0, NULL,
    0, NULL,
};

/* ----------------------------------------------------------------
 * xdg_toplevel interface
 * ---------------------------------------------------------------- */

static const struct wl_message xdg_toplevel_requests[] = {
    { "destroy",            "",     xdg_toplevel_request_types + 0 },
    { "set_parent",         "?o",   xdg_toplevel_request_types + 1 },
    { "set_title",          "s",    xdg_toplevel_request_types + 0 },
    { "set_app_id",         "s",    xdg_toplevel_request_types + 0 },
    { "show_window_menu",   "ouii", xdg_toplevel_request_types + 2 },
    { "move",               "ou",   xdg_toplevel_request_types + 3 },
    { "resize",             "ouu",  xdg_toplevel_request_types + 4 },
    { "set_max_size",       "ii",   xdg_toplevel_request_types + 0 },
    { "set_min_size",       "ii",   xdg_toplevel_request_types + 0 },
    { "set_maximized",      "",     xdg_toplevel_request_types + 0 },
    { "unset_maximized",    "",     xdg_toplevel_request_types + 0 },
    { "set_fullscreen",     "?o",   xdg_toplevel_fullscreen_types + 0 },
    { "unset_fullscreen",   "",     xdg_toplevel_request_types + 0 },
    { "set_minimized",      "",     xdg_toplevel_request_types + 0 },
};

static const struct wl_message xdg_toplevel_events[] = {
    { "configure",        "iia",  xdg_toplevel_request_types + 0 },
    { "close",            "",     xdg_toplevel_request_types + 0 },
    { "configure_bounds", "ii",   xdg_toplevel_request_types + 0 },
    { "wm_capabilities",  "a",    xdg_toplevel_request_types + 0 },
};

struct wl_interface xdg_toplevel_interface = {
    "xdg_toplevel", 6,
    14, xdg_toplevel_requests,
    4, xdg_toplevel_events,
};

/* ----------------------------------------------------------------
 * Init — fill in type arrays with runtime-loaded interfaces
 * ---------------------------------------------------------------- */

void lightrt_xdg_shell_init(const struct wl_interface *wl_surface_iface,
                             const struct wl_interface *wl_seat_iface,
                             const struct wl_interface *wl_output_iface) {
    /* xdg_wm_base types */
    xdg_wm_base_request_types[1] = &xdg_positioner_interface;
    xdg_wm_base_request_types[2] = &xdg_surface_interface;
    xdg_wm_base_request_types[3] = wl_surface_iface;

    /* xdg_surface types */
    xdg_surface_request_types[1] = &xdg_toplevel_interface;
    xdg_surface_request_types[2] = &xdg_popup_interface;
    xdg_surface_request_types[3] = &xdg_surface_interface;
    xdg_surface_request_types[4] = &xdg_positioner_interface;

    /* xdg_toplevel types */
    xdg_toplevel_request_types[1] = &xdg_toplevel_interface;
    xdg_toplevel_request_types[2] = wl_seat_iface;
    xdg_toplevel_request_types[3] = wl_seat_iface;
    xdg_toplevel_request_types[4] = wl_seat_iface;

    /* xdg_toplevel fullscreen type */
    xdg_toplevel_fullscreen_types[0] = wl_output_iface;
}

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_XDG_SHELL_IMPLEMENTATION */
