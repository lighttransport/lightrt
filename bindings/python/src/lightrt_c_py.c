#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <float.h>
#include <stdint.h>
#include <stdlib.h>

#include "lightrt_c.h"

typedef struct {
    PyObject_HEAD
    lrt_scene *scene;
    double *bounds; /* n * 6: lo[3], hi[3] */
    unsigned nprims;
    PyObject *intersect_cb;
} PyLrtScene;

static int py_float3(PyObject *obj, double out[3]) {
    PyObject *seq = PySequence_Fast(obj, "expected a 3-element sequence");
    if (!seq) return 0;
    if (PySequence_Fast_GET_SIZE(seq) != 3) {
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError, "expected a 3-element sequence");
        return 0;
    }
    for (Py_ssize_t i = 0; i < 3; i++) {
        out[i] = PyFloat_AsDouble(PySequence_Fast_GET_ITEM(seq, i));
        if (PyErr_Occurred()) {
            Py_DECREF(seq);
            return 0;
        }
    }
    Py_DECREF(seq);
    return 1;
}

static int py_bounds6(PyObject *obj, double out[6]) {
    PyObject *seq = PySequence_Fast(obj, "expected a bounds sequence");
    if (!seq) return 0;
    Py_ssize_t n = PySequence_Fast_GET_SIZE(seq);
    if (n == 6) {
        for (Py_ssize_t i = 0; i < 6; i++) {
            out[i] = PyFloat_AsDouble(PySequence_Fast_GET_ITEM(seq, i));
            if (PyErr_Occurred()) {
                Py_DECREF(seq);
                return 0;
            }
        }
        Py_DECREF(seq);
        return 1;
    }
    if (n == 2) {
        PyObject *lo = PySequence_Fast_GET_ITEM(seq, 0);
        PyObject *hi = PySequence_Fast_GET_ITEM(seq, 1);
        double l[3], h[3];
        int ok = py_float3(lo, l) && py_float3(hi, h);
        Py_DECREF(seq);
        if (!ok) return 0;
        for (int i = 0; i < 3; i++) {
            out[i] = l[i];
            out[i + 3] = h[i];
        }
        return 1;
    }
    Py_DECREF(seq);
    PyErr_SetString(PyExc_ValueError, "bounds must be [lo0,lo1,lo2,hi0,hi1,hi2] or [lo, hi]");
    return 0;
}

static lrt_aabb py_lrt_bounds(unsigned prim, void *user) {
    PyLrtScene *self = (PyLrtScene *)user;
    const double *b = self->bounds + (size_t)prim * 6u;
    lrt_aabb a;
    for (int i = 0; i < 3; i++) {
        a.lo[i] = b[i];
        a.hi[i] = b[i + 3];
    }
    return a;
}

static int py_parse_hit(PyObject *res, double *t, double *u, double *v) {
    if (res == Py_None || res == Py_False) return 0;
    if (PyFloat_Check(res) || PyLong_Check(res)) {
        *t = PyFloat_AsDouble(res);
        *u = 0.0;
        *v = 0.0;
        return !PyErr_Occurred();
    }
    PyObject *seq = PySequence_Fast(res, "intersect callback must return None, False, t, or (t,u,v)");
    if (!seq) return 0;
    Py_ssize_t n = PySequence_Fast_GET_SIZE(seq);
    if (n < 1 || n > 3) {
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError, "intersect callback result must have 1 to 3 values");
        return 0;
    }
    *t = PyFloat_AsDouble(PySequence_Fast_GET_ITEM(seq, 0));
    *u = (n > 1) ? PyFloat_AsDouble(PySequence_Fast_GET_ITEM(seq, 1)) : 0.0;
    *v = (n > 2) ? PyFloat_AsDouble(PySequence_Fast_GET_ITEM(seq, 2)) : 0.0;
    int ok = !PyErr_Occurred();
    Py_DECREF(seq);
    return ok;
}

static int py_lrt_intersect(const double org[3], const double dir[3],
                            double tmin, double tmax, unsigned prim,
                            void *user, double *t, double *u, double *v) {
    PyLrtScene *self = (PyLrtScene *)user;
    PyObject *org_obj = Py_BuildValue("(ddd)", org[0], org[1], org[2]);
    PyObject *dir_obj = Py_BuildValue("(ddd)", dir[0], dir[1], dir[2]);
    if (!org_obj || !dir_obj) {
        Py_XDECREF(org_obj);
        Py_XDECREF(dir_obj);
        return 0;
    }
    PyObject *res = PyObject_CallFunction(self->intersect_cb, "OOddI",
                                          org_obj, dir_obj, tmin, tmax, prim);
    Py_DECREF(org_obj);
    Py_DECREF(dir_obj);
    if (!res) return 0;
    int hit = py_parse_hit(res, t, u, v);
    Py_DECREF(res);
    if (PyErr_Occurred()) return 0;
    return hit;
}

static int PyLrtScene_init(PyLrtScene *self, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"bounds", "intersect", NULL};
    PyObject *bounds_obj = NULL;
    PyObject *intersect_cb = NULL;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "OO", kwlist,
                                     &bounds_obj, &intersect_cb)) {
        return -1;
    }
    if (!PyCallable_Check(intersect_cb)) {
        PyErr_SetString(PyExc_TypeError, "intersect must be callable");
        return -1;
    }
    PyObject *bounds_seq = PySequence_Fast(bounds_obj, "bounds must be a sequence");
    if (!bounds_seq) return -1;
    Py_ssize_t n = PySequence_Fast_GET_SIZE(bounds_seq);
    if (n <= 0 || n > UINT32_MAX) {
        Py_DECREF(bounds_seq);
        PyErr_SetString(PyExc_ValueError, "bounds must contain 1..UINT32_MAX primitives");
        return -1;
    }
    self->bounds = (double *)calloc((size_t)n * 6u, sizeof(double));
    if (!self->bounds) {
        Py_DECREF(bounds_seq);
        PyErr_NoMemory();
        return -1;
    }
    self->nprims = (unsigned)n;
    for (Py_ssize_t i = 0; i < n; i++) {
        if (!py_bounds6(PySequence_Fast_GET_ITEM(bounds_seq, i),
                        self->bounds + (size_t)i * 6u)) {
            Py_DECREF(bounds_seq);
            return -1;
        }
    }
    Py_DECREF(bounds_seq);
    Py_INCREF(intersect_cb);
    self->intersect_cb = intersect_cb;
    self->scene = lrt_scene_create(self->nprims, py_lrt_bounds, py_lrt_intersect, self);
    if (!self->scene) {
        PyErr_SetString(PyExc_MemoryError, "lrt_scene_create failed");
        return -1;
    }
    return 0;
}

static void PyLrtScene_dealloc(PyLrtScene *self) {
    if (self->scene) lrt_scene_free(self->scene);
    free(self->bounds);
    Py_XDECREF(self->intersect_cb);
    Py_TYPE(self)->tp_free((PyObject *)self);
}

static PyObject *PyLrtScene_build(PyLrtScene *self, PyObject *Py_UNUSED(args)) {
    if (!self->scene || !lrt_scene_build(self->scene)) {
        const char *err = self->scene ? lrt_scene_last_error(self->scene) : "scene is closed";
        PyErr_SetString(PyExc_RuntimeError, err);
        return NULL;
    }
    Py_RETURN_NONE;
}

static PyObject *PyLrtScene_intersect(PyLrtScene *self, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"org", "dir", "tmin", "tmax", NULL};
    PyObject *org_obj = NULL;
    PyObject *dir_obj = NULL;
    double tmin = 0.0;
    double tmax = DBL_MAX;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "OO|dd", kwlist,
                                     &org_obj, &dir_obj, &tmin, &tmax)) {
        return NULL;
    }
    double org[3], dir[3];
    if (!py_float3(org_obj, org) || !py_float3(dir_obj, dir)) return NULL;
    double t = 0.0, u = 0.0, v = 0.0;
    unsigned prim = lrt_scene_intersect(self->scene, org, dir, tmin, tmax, &t, &u, &v);
    if (PyErr_Occurred()) return NULL;
    if (prim == LRT_NO_HIT) {
        if (lrt_scene_last_result(self->scene) != LRT_RESULT_OK) {
            PyErr_SetString(PyExc_RuntimeError, lrt_scene_last_error(self->scene));
            return NULL;
        }
        Py_RETURN_NONE;
    }
    return Py_BuildValue("(Iddd)", prim, t, u, v);
}

static PyMethodDef PyLrtScene_methods[] = {
    {"build", (PyCFunction)PyLrtScene_build, METH_NOARGS, "Build the CPU BVH."},
    {"intersect", (PyCFunction)PyLrtScene_intersect, METH_VARARGS | METH_KEYWORDS,
     "Trace one ray. Returns (prim_id, t, u, v) or None."},
    {NULL, NULL, 0, NULL}
};

static PyTypeObject PyLrtSceneType = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "lightrt_c.Scene",
    .tp_basicsize = sizeof(PyLrtScene),
    .tp_dealloc = (destructor)PyLrtScene_dealloc,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_doc = "LightRT C11 CPU callback scene",
    .tp_methods = PyLrtScene_methods,
    .tp_init = (initproc)PyLrtScene_init,
    .tp_new = PyType_GenericNew,
};

static PyObject *py_backend_name(PyObject *self, PyObject *args) {
    (void)self;
    (void)args;
    return PyUnicode_FromString(lrt_backend_name());
}

static PyMethodDef module_methods[] = {
    {"backend_name", py_backend_name, METH_NOARGS, "Return the C backend name."},
    {NULL, NULL, 0, NULL}
};

static struct PyModuleDef moduledef = {
    PyModuleDef_HEAD_INIT,
    .m_name = "_lightrt_c",
    .m_doc = "Native bindings for LightRT C11 CPU callback BVH",
    .m_size = -1,
    .m_methods = module_methods,
};

PyMODINIT_FUNC PyInit__lightrt_c(void) {
    if (PyType_Ready(&PyLrtSceneType) < 0) return NULL;
    PyObject *m = PyModule_Create(&moduledef);
    if (!m) return NULL;
    Py_INCREF(&PyLrtSceneType);
    if (PyModule_AddObject(m, "Scene", (PyObject *)&PyLrtSceneType) < 0) {
        Py_DECREF(&PyLrtSceneType);
        Py_DECREF(m);
        return NULL;
    }
    PyModule_AddIntConstant(m, "NO_HIT", (long)LRT_NO_HIT);
    return m;
}
