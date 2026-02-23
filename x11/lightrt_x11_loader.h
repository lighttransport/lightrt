/*
 * lightrt_x11_loader.h — Runtime loader for libX11.so.6 via dlopen/dlsym.
 *
 * Single-header library. Define LIGHTRT_X11_IMPLEMENTATION in exactly one
 * .c/.cc file before including this header to get the implementation.
 *
 * Usage:
 *   #include "x11/lightrt_x11.h"
 *   #define LIGHTRT_X11_IMPLEMENTATION
 *   #include "x11/lightrt_x11_loader.h"
 *
 *   // In main():
 *   if (lightrt_x11_load(&g_x11_) != 0) { error; }
 *   // ... use X11 calls normally (redirected via macros) ...
 *   lightrt_x11_unload(&g_x11_);
 */

#ifndef LIGHTRT_X11_LOADER_H
#define LIGHTRT_X11_LOADER_H

#include "lightrt_x11.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ================================================================
 * Function pointer table — all X11 functions used by viewer_x11
 * ================================================================ */

typedef struct LightrtX11 {
    void *handle;  /* dlopen handle */

    /* Display management */
    Display*      (*XOpenDisplay)(const char *);
    int           (*XCloseDisplay)(Display *);

    /* Screen accessors (function versions of Xlib macros) */
    int           (*XDefaultScreen)(Display *);
    Window        (*XRootWindow)(Display *, int);
    Visual*       (*XDefaultVisual)(Display *, int);
    int           (*XDefaultDepth)(Display *, int);
    unsigned long (*XBlackPixel)(Display *, int);

    /* Window management */
    Window (*XCreateWindow)(Display *, Window, int, int, unsigned int,
                            unsigned int, unsigned int, int, unsigned int,
                            Visual *, unsigned long, XSetWindowAttributes *);
    int    (*XMapWindow)(Display *, Window);
    int    (*XDestroyWindow)(Display *, Window);
    int    (*XStoreName)(Display *, Window, const char *);

    /* Atoms / WM protocols */
    Atom   (*XInternAtom)(Display *, const char *, Bool);
    Status (*XSetWMProtocols)(Display *, Window, Atom *, int);

    /* Graphics context */
    GC     (*XCreateGC)(Display *, Drawable, unsigned long, void *);
    int    (*XFreeGC)(Display *, GC);

    /* Image */
    XImage* (*XCreateImage)(Display *, Visual *, unsigned int, int, int,
                            char *, unsigned int, unsigned int, int, int);
    int     (*XPutImage)(Display *, Drawable, GC, XImage *, int, int,
                         int, int, unsigned int, unsigned int);

    /* Events */
    int    (*XPending)(Display *);
    int    (*XNextEvent)(Display *, XEvent *);
    int    (*XEventsQueued)(Display *, int);
    int    (*XPeekEvent)(Display *, XEvent *);
    KeySym (*XLookupKeysym)(XKeyEvent *, int);

    /* Misc */
    int    (*XFlush)(Display *);
} LightrtX11;

/* Global instance used by macro redirects below */
static LightrtX11 g_x11_;

/* Loader API */
static int  lightrt_x11_load(LightrtX11 *x11);
static void lightrt_x11_unload(LightrtX11 *x11);

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_X11_LOADER_H */

/* ================================================================
 * Implementation — compiled when LIGHTRT_X11_IMPLEMENTATION is defined.
 * MUST appear before the macro redirects so the raw member names are
 * visible inside lightrt_x11_load().
 * ================================================================ */

#ifdef LIGHTRT_X11_IMPLEMENTATION
#undef LIGHTRT_X11_IMPLEMENTATION

#include <dlfcn.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Helper macro — load one symbol, fail if missing */
#define LIGHTRT_X11_LOAD_SYM(x11, name)                                \
    do {                                                                \
        *((void **)&(x11)->name) = dlsym((x11)->handle, #name);        \
        if (!(x11)->name) return -1;                                    \
    } while (0)

static int lightrt_x11_load(LightrtX11 *x11) {
    memset(x11, 0, sizeof(*x11));

    /* Try standard soname, then fallback */
    x11->handle = dlopen("libX11.so.6", RTLD_LAZY);
    if (!x11->handle)
        x11->handle = dlopen("libX11.so", RTLD_LAZY);
    if (!x11->handle)
        return -1;

    /* Display management */
    LIGHTRT_X11_LOAD_SYM(x11, XOpenDisplay);
    LIGHTRT_X11_LOAD_SYM(x11, XCloseDisplay);

    /* Screen accessors */
    LIGHTRT_X11_LOAD_SYM(x11, XDefaultScreen);
    LIGHTRT_X11_LOAD_SYM(x11, XRootWindow);
    LIGHTRT_X11_LOAD_SYM(x11, XDefaultVisual);
    LIGHTRT_X11_LOAD_SYM(x11, XDefaultDepth);
    LIGHTRT_X11_LOAD_SYM(x11, XBlackPixel);

    /* Window management */
    LIGHTRT_X11_LOAD_SYM(x11, XCreateWindow);
    LIGHTRT_X11_LOAD_SYM(x11, XMapWindow);
    LIGHTRT_X11_LOAD_SYM(x11, XDestroyWindow);
    LIGHTRT_X11_LOAD_SYM(x11, XStoreName);

    /* Atoms / WM protocols */
    LIGHTRT_X11_LOAD_SYM(x11, XInternAtom);
    LIGHTRT_X11_LOAD_SYM(x11, XSetWMProtocols);

    /* Graphics context */
    LIGHTRT_X11_LOAD_SYM(x11, XCreateGC);
    LIGHTRT_X11_LOAD_SYM(x11, XFreeGC);

    /* Image */
    LIGHTRT_X11_LOAD_SYM(x11, XCreateImage);
    LIGHTRT_X11_LOAD_SYM(x11, XPutImage);

    /* Events */
    LIGHTRT_X11_LOAD_SYM(x11, XPending);
    LIGHTRT_X11_LOAD_SYM(x11, XNextEvent);
    LIGHTRT_X11_LOAD_SYM(x11, XEventsQueued);
    LIGHTRT_X11_LOAD_SYM(x11, XPeekEvent);
    LIGHTRT_X11_LOAD_SYM(x11, XLookupKeysym);

    /* Misc */
    LIGHTRT_X11_LOAD_SYM(x11, XFlush);

    return 0;
}

#undef LIGHTRT_X11_LOAD_SYM

static void lightrt_x11_unload(LightrtX11 *x11) {
    if (x11->handle) {
        dlclose(x11->handle);
        x11->handle = 0;
    }
}

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_X11_IMPLEMENTATION */

/* ================================================================
 * Macro redirects — make X11 calls go through the loader.
 * These MUST come after the implementation section so that
 * lightrt_x11_load() sees the raw struct member names.
 * ================================================================ */

#ifndef LIGHTRT_X11_MACROS_DEFINED_
#define LIGHTRT_X11_MACROS_DEFINED_

/* Regular functions */
#define XOpenDisplay      g_x11_.XOpenDisplay
#define XCloseDisplay     g_x11_.XCloseDisplay
#define XCreateWindow     g_x11_.XCreateWindow
#define XMapWindow        g_x11_.XMapWindow
#define XDestroyWindow    g_x11_.XDestroyWindow
#define XStoreName        g_x11_.XStoreName
#define XInternAtom       g_x11_.XInternAtom
#define XSetWMProtocols   g_x11_.XSetWMProtocols
#define XCreateGC         g_x11_.XCreateGC
#define XFreeGC           g_x11_.XFreeGC
#define XCreateImage      g_x11_.XCreateImage
#define XPutImage         g_x11_.XPutImage
#define XPending          g_x11_.XPending
#define XNextEvent        g_x11_.XNextEvent
#define XEventsQueued     g_x11_.XEventsQueued
#define XPeekEvent        g_x11_.XPeekEvent
#define XLookupKeysym     g_x11_.XLookupKeysym
#define XFlush            g_x11_.XFlush

/* Display accessor macros — Xlib defines these as struct-field accesses
 * into the opaque Display. We use the function versions instead. */
#define DefaultScreen(d)     g_x11_.XDefaultScreen(d)
#define RootWindow(d,s)      g_x11_.XRootWindow(d,s)
#define DefaultVisual(d,s)   g_x11_.XDefaultVisual(d,s)
#define DefaultDepth(d,s)    g_x11_.XDefaultDepth(d,s)
#define BlackPixel(d,s)      g_x11_.XBlackPixel(d,s)

#endif /* LIGHTRT_X11_MACROS_DEFINED_ */
