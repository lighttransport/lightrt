/*
 * lightrt_wayland.h — Minimal Wayland type definitions for LightRT viewer.
 *
 * ABI-compatible with libwayland-client on LP64 Linux (64-bit).
 * Only types, structs, and constants actually used by viewer_wayland are defined.
 * This eliminates the compile-time dependency on libwayland-dev headers.
 *
 * Protocol details derived from wayland.xml (Wayland core protocol).
 */

#ifndef LIGHTRT_WAYLAND_H
#define LIGHTRT_WAYLAND_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ================================================================
 * Core Wayland types (from wayland-util.h, wayland-client-core.h)
 * ================================================================ */

typedef int32_t wl_fixed_t;

struct wl_interface;

struct wl_message {
    const char *name;
    const char *signature;
    const struct wl_interface **types;
};

struct wl_interface {
    const char *name;
    int version;
    int method_count;
    const struct wl_message *methods;
    int event_count;
    const struct wl_message *events;
};

struct wl_array {
    size_t size;
    size_t alloc;
    void *data;
};

struct wl_list {
    struct wl_list *prev;
    struct wl_list *next;
};

/* ================================================================
 * Opaque protocol types (forward declarations)
 * ================================================================ */

struct wl_proxy;
struct wl_display;
struct wl_registry;
struct wl_compositor;
struct wl_surface;
struct wl_shm;
struct wl_shm_pool;
struct wl_buffer;
struct wl_callback;
struct wl_seat;
struct wl_keyboard;
struct wl_pointer;
struct wl_output;
struct wl_region;

/* ================================================================
 * Fixed-point conversion (matches wayland-util.h)
 * ================================================================ */

static inline double
wl_fixed_to_double(wl_fixed_t f) {
    union { double d; int64_t i; } u;
    u.i = ((1023LL + 44LL) << 52) + (1LL << 51) + f;
    return u.d - (3LL << 43);
}

/* ================================================================
 * Listener structs — function pointer tables for events we handle
 * Must match the exact event ordering from wayland.xml.
 * ================================================================ */

struct wl_registry_listener {
    void (*global)(void *data, struct wl_registry *registry,
                   uint32_t name, const char *interface, uint32_t version);
    void (*global_remove)(void *data, struct wl_registry *registry,
                          uint32_t name);
};

struct wl_callback_listener {
    void (*done)(void *data, struct wl_callback *callback,
                 uint32_t callback_data);
};

struct wl_buffer_listener {
    void (*release)(void *data, struct wl_buffer *buffer);
};

struct wl_shm_listener {
    void (*format)(void *data, struct wl_shm *shm, uint32_t format);
};

struct wl_seat_listener {
    void (*capabilities)(void *data, struct wl_seat *seat,
                         uint32_t capabilities);
    void (*name)(void *data, struct wl_seat *seat, const char *name);
};

struct wl_keyboard_listener {
    void (*keymap)(void *data, struct wl_keyboard *keyboard,
                   uint32_t format, int32_t fd, uint32_t size);
    void (*enter)(void *data, struct wl_keyboard *keyboard,
                  uint32_t serial, struct wl_surface *surface,
                  struct wl_array *keys);
    void (*leave)(void *data, struct wl_keyboard *keyboard,
                  uint32_t serial, struct wl_surface *surface);
    void (*key)(void *data, struct wl_keyboard *keyboard,
                uint32_t serial, uint32_t time, uint32_t key,
                uint32_t state);
    void (*modifiers)(void *data, struct wl_keyboard *keyboard,
                      uint32_t serial, uint32_t mods_depressed,
                      uint32_t mods_latched, uint32_t mods_locked,
                      uint32_t group);
    void (*repeat_info)(void *data, struct wl_keyboard *keyboard,
                        int32_t rate, int32_t delay);
};

struct wl_pointer_listener {
    void (*enter)(void *data, struct wl_pointer *pointer,
                  uint32_t serial, struct wl_surface *surface,
                  wl_fixed_t sx, wl_fixed_t sy);
    void (*leave)(void *data, struct wl_pointer *pointer,
                  uint32_t serial, struct wl_surface *surface);
    void (*motion)(void *data, struct wl_pointer *pointer,
                   uint32_t time, wl_fixed_t sx, wl_fixed_t sy);
    void (*button)(void *data, struct wl_pointer *pointer,
                   uint32_t serial, uint32_t time, uint32_t button,
                   uint32_t state);
    void (*axis)(void *data, struct wl_pointer *pointer,
                 uint32_t time, uint32_t axis, wl_fixed_t value);
    void (*frame)(void *data, struct wl_pointer *pointer);
    void (*axis_source)(void *data, struct wl_pointer *pointer,
                        uint32_t axis_source);
    void (*axis_stop)(void *data, struct wl_pointer *pointer,
                      uint32_t time, uint32_t axis);
    void (*axis_discrete)(void *data, struct wl_pointer *pointer,
                          uint32_t axis, int32_t discrete);
    void (*axis_value120)(void *data, struct wl_pointer *pointer,
                          uint32_t axis, int32_t value120);
    void (*axis_relative_direction)(void *data, struct wl_pointer *pointer,
                                    uint32_t axis, uint32_t direction);
};

/* ================================================================
 * Request opcodes (from wayland.xml)
 * ================================================================ */

/* wl_display requests */
#define WL_DISPLAY_SYNC                 0
#define WL_DISPLAY_GET_REGISTRY         1

/* wl_registry requests */
#define WL_REGISTRY_BIND                0

/* wl_compositor requests */
#define WL_COMPOSITOR_CREATE_SURFACE    0
#define WL_COMPOSITOR_CREATE_REGION     1

/* wl_surface requests */
#define WL_SURFACE_DESTROY              0
#define WL_SURFACE_ATTACH               1
#define WL_SURFACE_DAMAGE               2
#define WL_SURFACE_FRAME                3
#define WL_SURFACE_SET_OPAQUE_REGION    4
#define WL_SURFACE_SET_INPUT_REGION     5
#define WL_SURFACE_COMMIT               6
#define WL_SURFACE_DAMAGE_BUFFER        9

/* wl_shm requests */
#define WL_SHM_CREATE_POOL             0

/* wl_shm_pool requests */
#define WL_SHM_POOL_CREATE_BUFFER      0
#define WL_SHM_POOL_DESTROY            1

/* wl_buffer requests */
#define WL_BUFFER_DESTROY              0

/* wl_seat requests */
#define WL_SEAT_GET_POINTER            0
#define WL_SEAT_GET_KEYBOARD           1

/* wl_callback (no requests, only done event) */

/* ================================================================
 * Constants
 * ================================================================ */

/* SHM pixel formats */
#define WL_SHM_FORMAT_ARGB8888         0
#define WL_SHM_FORMAT_XRGB8888         1

/* Seat capabilities */
#define WL_SEAT_CAPABILITY_POINTER     1
#define WL_SEAT_CAPABILITY_KEYBOARD    2

/* Pointer button state */
#define WL_POINTER_BUTTON_STATE_RELEASED  0
#define WL_POINTER_BUTTON_STATE_PRESSED   1

/* Keyboard key state */
#define WL_KEYBOARD_KEY_STATE_RELEASED    0
#define WL_KEYBOARD_KEY_STATE_PRESSED     1

/* Keyboard keymap format */
#define WL_KEYBOARD_KEYMAP_FORMAT_XKB_V1  1

/* Marshal flags */
#define WL_MARSHAL_FLAG_DESTROY        1

/* Linux input event codes for mouse buttons */
#define BTN_LEFT                       0x110
#define BTN_RIGHT                      0x111
#define BTN_MIDDLE                     0x112

/* Scroll axis */
#define WL_POINTER_AXIS_VERTICAL_SCROLL   0
#define WL_POINTER_AXIS_HORIZONTAL_SCROLL 1

/* ================================================================
 * xkbcommon types and constants (from xkbcommon/xkbcommon.h)
 * ================================================================ */

struct xkb_context;
struct xkb_keymap;
struct xkb_state;

enum xkb_context_flags {
    XKB_CONTEXT_NO_FLAGS = 0
};

enum xkb_keymap_format {
    XKB_KEYMAP_FORMAT_TEXT_V1 = 1
};

enum xkb_keymap_compile_flags {
    XKB_KEYMAP_COMPILE_NO_FLAGS = 0
};

/* xkbcommon keysym values (same numeric values as X11 keysyms) */
#define XKB_KEY_Escape      0xff1b
#define XKB_KEY_Tab         0xff09
#define XKB_KEY_Shift_L     0xffe1
#define XKB_KEY_Shift_R     0xffe2
#define XKB_KEY_Control_L   0xffe3
#define XKB_KEY_Control_R   0xffe4
#define XKB_KEY_Alt_L       0xffe9
#define XKB_KEY_Alt_R       0xffea
#define XKB_KEY_f           0x0066
#define XKB_KEY_F           0x0046
#define XKB_KEY_s           0x0073
#define XKB_KEY_S           0x0053
#define XKB_KEY_o           0x006f
#define XKB_KEY_O           0x004f
#define XKB_KEY_plus        0x002b
#define XKB_KEY_equal       0x003d

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_WAYLAND_H */
