/*
 * lightrt_x11.h — Minimal X11 type definitions for LightRT viewer.
 *
 * ABI-compatible with Xlib on LP64 Linux (64-bit).
 * Only types, structs, and constants actually used by viewer_x11 are defined.
 * This eliminates the compile-time dependency on libx11-dev headers.
 */

#ifndef LIGHTRT_X11_H
#define LIGHTRT_X11_H

#ifdef __cplusplus
extern "C" {
#endif

/* ================================================================
 * Basic X11 types (from X11/X.h, X11/Xlib.h)
 * All match LP64 ABI: long = 8 bytes, pointer = 8 bytes
 * ================================================================ */

typedef unsigned long XID;
typedef XID           Window;
typedef XID           Drawable;
typedef XID           Pixmap;
typedef XID           Colormap;
typedef XID           Cursor;
typedef unsigned long Atom;
typedef unsigned long VisualID;
typedef unsigned long Time;
typedef unsigned long KeySym;
typedef int           Bool;
typedef int           Status;

/* Opaque types — internal layout managed by Xlib */
typedef struct _XDisplay Display;
typedef struct _XGC     *GC;
typedef struct _Visual   Visual;  /* only passed as pointer, never dereferenced */
typedef struct _XScreen  Screen;  /* only passed as pointer, never dereferenced */

/* ================================================================
 * XSetWindowAttributes — 15 fields, ABI-exact layout on LP64
 * Viewer uses: background_pixel, event_mask
 * ================================================================ */

typedef struct {
    Pixmap        background_pixmap;       /*  0: unsigned long (8) */
    unsigned long background_pixel;        /*  8: unsigned long (8) */
    Pixmap        border_pixmap;           /* 16: unsigned long (8) */
    unsigned long border_pixel;            /* 24: unsigned long (8) */
    int           bit_gravity;             /* 32: int (4) */
    int           win_gravity;             /* 36: int (4) */
    int           backing_store;           /* 40: int (4) + 4 pad */
    unsigned long backing_planes;          /* 48: unsigned long (8) */
    unsigned long backing_pixel;           /* 56: unsigned long (8) */
    Bool          save_under;              /* 64: int (4) + 4 pad */
    long          event_mask;              /* 72: long (8) */
    long          do_not_propagate_mask;   /* 80: long (8) */
    Bool          override_redirect;       /* 88: int (4) + 4 pad */
    Colormap      colormap;                /* 96: unsigned long (8) */
    Cursor        cursor;                  /* 104: unsigned long (8) */
} XSetWindowAttributes;                    /* total: 112 bytes */

/* ================================================================
 * XImage — viewer accesses ->data (offset 16) and ->byte_order (offset 24)
 * Full struct needed for ABI compat with XCreateImage/XDestroyImage
 * ================================================================ */

typedef struct _XImage {
    int            width, height;          /*  0,  4: int (4+4) */
    int            xoffset;                /*  8: int (4) */
    int            format;                 /* 12: int (4) */
    char          *data;                   /* 16: pointer (8) */
    int            byte_order;             /* 24: int (4) */
    int            bitmap_unit;            /* 28: int (4) */
    int            bitmap_bit_order;       /* 32: int (4) */
    int            bitmap_pad;             /* 36: int (4) */
    int            depth;                  /* 40: int (4) */
    int            bytes_per_line;         /* 44: int (4) */
    int            bits_per_pixel;         /* 48: int (4) + 4 pad */
    unsigned long  red_mask;               /* 56: unsigned long (8) */
    unsigned long  green_mask;             /* 64: unsigned long (8) */
    unsigned long  blue_mask;              /* 72: unsigned long (8) */
    char          *obdata;                 /* 80: pointer (8) */
    struct {                               /* 88: function pointer table */
        struct _XImage *(*create_image)(
            Display*, Visual*, unsigned int, int, int,
            char*, unsigned int, unsigned int, int, int);
        int (*destroy_image)(struct _XImage *);
        unsigned long (*get_pixel)(struct _XImage *, int, int);
        int (*put_pixel)(struct _XImage *, int, int, unsigned long);
        struct _XImage *(*sub_image)(
            struct _XImage *, int, int, unsigned int, unsigned int);
        int (*add_pixel)(struct _XImage *, long);
    } f;                                   /* 6 pointers * 8 = 48 bytes */
} XImage;                                  /* total: 136 bytes */

/* XDestroyImage is a macro in Xlib, using the XImage function table */
#define XDestroyImage(ximage) ((*((ximage)->f.destroy_image))((ximage)))

/* ================================================================
 * XEvent sub-structs — must match Xlib field order and LP64 alignment
 * ================================================================ */

/* Common header for all events */
typedef struct {
    int            type;                   /*  0: int (4) + 4 pad */
    unsigned long  serial;                 /*  8: unsigned long (8) */
    Bool           send_event;             /* 16: int (4) + 4 pad */
    Display       *display;                /* 24: pointer (8) */
    Window         window;                 /* 32: unsigned long (8) */
} XAnyEvent;                               /* 40 bytes */

typedef struct {
    int            type;
    unsigned long  serial;
    Bool           send_event;
    Display       *display;
    Window         window;
    Window         root;                   /* 40 */
    Window         subwindow;              /* 48 */
    Time           time;                   /* 56 */
    int            x, y;                   /* 64, 68 */
    int            x_root, y_root;         /* 72, 76 */
    unsigned int   state;                  /* 80 */
    unsigned int   keycode;                /* 84 */
    Bool           same_screen;            /* 88 */
} XKeyEvent;

typedef struct {
    int            type;
    unsigned long  serial;
    Bool           send_event;
    Display       *display;
    Window         window;
    Window         root;
    Window         subwindow;
    Time           time;
    int            x, y;
    int            x_root, y_root;
    unsigned int   state;
    unsigned int   button;                 /* same offset as keycode */
    Bool           same_screen;
} XButtonEvent;

typedef struct {
    int            type;
    unsigned long  serial;
    Bool           send_event;
    Display       *display;
    Window         window;
    Window         root;
    Window         subwindow;
    Time           time;
    int            x, y;
    int            x_root, y_root;
    unsigned int   state;
    char           is_hint;                /* 84: char (1) + 3 pad */
    Bool           same_screen;            /* 88: int (4) */
} XMotionEvent;

typedef struct {
    int            type;
    unsigned long  serial;
    Bool           send_event;
    Display       *display;
    Window         event;                  /* 32: the event window */
    Window         window;                 /* 40: the window */
    int            x, y;                   /* 48, 52 */
    int            width, height;          /* 56, 60 */
    int            border_width;           /* 64: int (4) + 4 pad */
    Window         above;                  /* 72: unsigned long (8) */
    Bool           override_redirect;      /* 80: int (4) */
} XConfigureEvent;

typedef struct {
    int            type;
    unsigned long  serial;
    Bool           send_event;
    Display       *display;
    Window         window;
    Atom           message_type;           /* 40 */
    int            format;                 /* 48: int (4) + 4 pad */
    union {
        char  b[20];
        short s[10];
        long  l[5];                        /* 5 * 8 = 40 bytes on LP64 */
    } data;                                /* 56 */
} XClientMessageEvent;

/* XEvent union — 192 bytes on LP64 (24 * sizeof(long)) */
typedef union _XEvent {
    int                   type;
    XAnyEvent             xany;
    XKeyEvent             xkey;
    XButtonEvent          xbutton;
    XMotionEvent          xmotion;
    XConfigureEvent       xconfigure;
    XClientMessageEvent   xclient;
    long                  pad[24];
} XEvent;

/* ================================================================
 * Constants
 * ================================================================ */

/* Event masks */
#define KeyPressMask            (1L<<0)
#define KeyReleaseMask          (1L<<1)
#define ButtonPressMask         (1L<<2)
#define ButtonReleaseMask       (1L<<3)
#define PointerMotionMask       (1L<<6)
#define ExposureMask            (1L<<15)
#define StructureNotifyMask     (1L<<17)

/* CreateWindow attribute flags */
#define CWBackPixel             (1L<<1)
#define CWEventMask             (1L<<11)

/* Event types */
#define KeyPress                2
#define KeyRelease              3
#define ButtonPress             4
#define ButtonRelease           5
#define MotionNotify            6
#define ConfigureNotify         22
#define ClientMessage           33

/* Image format */
#define ZPixmap                 2

/* Byte order */
#define LSBFirst                0

/* Window class */
#define InputOutput             1

/* Mouse buttons */
#define Button1                 1
#define Button2                 2
#define Button3                 3
#define Button4                 4
#define Button5                 5

/* Bool values */
#ifndef True
#define True                    1
#endif
#ifndef False
#define False                   0
#endif

/* XEventsQueued mode */
#define QueuedAfterReading      1

/* ================================================================
 * KeySym values (from X11/keysymdef.h)
 * ================================================================ */

#define XK_Escape               0xff1b
#define XK_Tab                  0xff09
#define XK_Shift_L              0xffe1
#define XK_Shift_R              0xffe2
#define XK_Control_L            0xffe3
#define XK_Control_R            0xffe4
#define XK_Alt_L                0xffe9
#define XK_Alt_R                0xffea
#define XK_f                    0x0066
#define XK_F                    0x0046
#define XK_s                    0x0073
#define XK_S                    0x0053
#define XK_o                    0x006f
#define XK_O                    0x004f
#define XK_plus                 0x002b
#define XK_equal                0x003d
#define XK_minus                0x002d
#define XK_underscore           0x005f
#define XK_b                    0x0062
#define XK_B                    0x0042
#define XK_v                    0x0076
#define XK_V                    0x0056
#define XK_h                    0x0068
#define XK_H                    0x0048
#define XK_r                    0x0072
#define XK_R                    0x0052
#define XK_bracketleft          0x005b
#define XK_bracketright         0x005d

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_X11_H */
