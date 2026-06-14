#include <float.h>
#include <node_api.h>
#include <stdint.h>
#include <stdlib.h>

#include "lightrt_c.h"

typedef struct {
    napi_env env;
    napi_ref wrapper;
    napi_ref callback;
    lrt_scene *scene;
    double *bounds; /* n * 6: lo[3], hi[3] */
    unsigned nprims;
    int callback_failed;
} node_scene;

static napi_ref g_scene_ctor;

static void throw_status(napi_env env, napi_status status, const char *msg) {
    if (status != napi_ok) napi_throw_error(env, NULL, msg);
}

static int get_float3(napi_env env, napi_value value, double out[3]) {
    bool is_array = false;
    if (napi_is_array(env, value, &is_array) != napi_ok || !is_array) {
        napi_throw_type_error(env, NULL, "expected a 3-element array");
        return 0;
    }
    uint32_t len = 0;
    napi_get_array_length(env, value, &len);
    if (len != 3) {
        napi_throw_range_error(env, NULL, "expected a 3-element array");
        return 0;
    }
    for (uint32_t i = 0; i < 3; i++) {
        napi_value item;
        if (napi_get_element(env, value, i, &item) != napi_ok ||
            napi_get_value_double(env, item, &out[i]) != napi_ok) {
            napi_throw_type_error(env, NULL, "expected numeric vector elements");
            return 0;
        }
    }
    return 1;
}

static int get_bounds6(napi_env env, napi_value value, double out[6]) {
    bool is_array = false;
    if (napi_is_array(env, value, &is_array) != napi_ok || !is_array) {
        napi_throw_type_error(env, NULL, "bounds must be an array");
        return 0;
    }
    uint32_t len = 0;
    napi_get_array_length(env, value, &len);
    if (len == 6) {
        for (uint32_t i = 0; i < 6; i++) {
            napi_value item;
            if (napi_get_element(env, value, i, &item) != napi_ok ||
                napi_get_value_double(env, item, &out[i]) != napi_ok) {
                napi_throw_type_error(env, NULL, "bounds elements must be numbers");
                return 0;
            }
        }
        return 1;
    }
    if (len == 2) {
        napi_value lo, hi;
        double l[3], h[3];
        if (napi_get_element(env, value, 0, &lo) != napi_ok ||
            napi_get_element(env, value, 1, &hi) != napi_ok ||
            !get_float3(env, lo, l) || !get_float3(env, hi, h)) {
            return 0;
        }
        for (int i = 0; i < 3; i++) {
            out[i] = l[i];
            out[i + 3] = h[i];
        }
        return 1;
    }
    napi_throw_range_error(env, NULL, "bounds must be [lo0,lo1,lo2,hi0,hi1,hi2] or [lo, hi]");
    return 0;
}

static lrt_aabb node_lrt_bounds(unsigned prim, void *user) {
    node_scene *s = (node_scene *)user;
    const double *b = s->bounds + (size_t)prim * 6u;
    lrt_aabb a;
    for (int i = 0; i < 3; i++) {
        a.lo[i] = b[i];
        a.hi[i] = b[i + 3];
    }
    return a;
}

static napi_value make_vec3(napi_env env, const double v[3]) {
    napi_value arr;
    napi_create_array_with_length(env, 3, &arr);
    for (uint32_t i = 0; i < 3; i++) {
        napi_value n;
        napi_create_double(env, v[i], &n);
        napi_set_element(env, arr, i, n);
    }
    return arr;
}

static int parse_hit(napi_env env, napi_value result, double *t, double *u, double *v) {
    napi_valuetype type;
    if (napi_typeof(env, result, &type) != napi_ok) return 0;
    if (type == napi_null || type == napi_undefined) return 0;
    if (type == napi_boolean) {
        bool b = false;
        napi_get_value_bool(env, result, &b);
        if (!b) return 0;
    }
    if (type == napi_number) {
        *u = 0.0;
        *v = 0.0;
        return napi_get_value_double(env, result, t) == napi_ok;
    }
    bool is_array = false;
    if (napi_is_array(env, result, &is_array) != napi_ok || !is_array) {
        napi_throw_type_error(env, NULL, "intersect callback must return null, false, t, or [t,u,v]");
        return 0;
    }
    uint32_t len = 0;
    napi_get_array_length(env, result, &len);
    if (len < 1 || len > 3) {
        napi_throw_range_error(env, NULL, "intersect callback result must have 1 to 3 values");
        return 0;
    }
    napi_value item;
    if (napi_get_element(env, result, 0, &item) != napi_ok ||
        napi_get_value_double(env, item, t) != napi_ok) {
        napi_throw_type_error(env, NULL, "hit t must be numeric");
        return 0;
    }
    *u = 0.0;
    *v = 0.0;
    if (len > 1) {
        if (napi_get_element(env, result, 1, &item) != napi_ok ||
            napi_get_value_double(env, item, u) != napi_ok) {
            napi_throw_type_error(env, NULL, "hit u must be numeric");
            return 0;
        }
    }
    if (len > 2) {
        if (napi_get_element(env, result, 2, &item) != napi_ok ||
            napi_get_value_double(env, item, v) != napi_ok) {
            napi_throw_type_error(env, NULL, "hit v must be numeric");
            return 0;
        }
    }
    return 1;
}

static int node_lrt_intersect(const double org[3], const double dir[3],
                              double tmin, double tmax, unsigned prim,
                              void *user, double *t, double *u, double *v) {
    node_scene *s = (node_scene *)user;
    napi_env env = s->env;
    napi_value cb, global, argv[5], result;
    if (napi_get_reference_value(env, s->callback, &cb) != napi_ok ||
        napi_get_global(env, &global) != napi_ok) {
        s->callback_failed = 1;
        return 0;
    }
    argv[0] = make_vec3(env, org);
    argv[1] = make_vec3(env, dir);
    napi_create_double(env, tmin, &argv[2]);
    napi_create_double(env, tmax, &argv[3]);
    napi_create_uint32(env, prim, &argv[4]);
    if (napi_call_function(env, global, cb, 5, argv, &result) != napi_ok) {
        s->callback_failed = 1;
        return 0;
    }
    int hit = parse_hit(env, result, t, u, v);
    bool pending = false;
    napi_is_exception_pending(env, &pending);
    if (pending) s->callback_failed = 1;
    return pending ? 0 : hit;
}

static void scene_finalize(napi_env env, void *data, void *hint) {
    (void)hint;
    node_scene *s = (node_scene *)data;
    if (!s) return;
    if (s->scene) lrt_scene_free(s->scene);
    if (s->callback) napi_delete_reference(env, s->callback);
    if (s->wrapper) napi_delete_reference(env, s->wrapper);
    free(s->bounds);
    free(s);
}

static napi_value Scene_new(napi_env env, napi_callback_info info) {
    size_t argc = 2;
    napi_value args[2], thisv;
    napi_get_cb_info(env, info, &argc, args, &thisv, NULL);
    if (argc < 2) {
        napi_throw_type_error(env, NULL, "Scene(bounds, intersect) requires two arguments");
        return NULL;
    }
    napi_valuetype cb_type;
    napi_typeof(env, args[1], &cb_type);
    if (cb_type != napi_function) {
        napi_throw_type_error(env, NULL, "intersect must be a function");
        return NULL;
    }
    bool is_array = false;
    if (napi_is_array(env, args[0], &is_array) != napi_ok || !is_array) {
        napi_throw_type_error(env, NULL, "bounds must be an array");
        return NULL;
    }
    uint32_t n = 0;
    napi_get_array_length(env, args[0], &n);
    if (n == 0) {
        napi_throw_range_error(env, NULL, "bounds must contain at least one primitive");
        return NULL;
    }

    node_scene *s = (node_scene *)calloc(1, sizeof(node_scene));
    if (!s) {
        napi_throw_error(env, NULL, "out of memory");
        return NULL;
    }
    s->env = env;
    s->nprims = n;
    s->bounds = (double *)calloc((size_t)n * 6u, sizeof(double));
    if (!s->bounds) {
        free(s);
        napi_throw_error(env, NULL, "out of memory");
        return NULL;
    }
    for (uint32_t i = 0; i < n; i++) {
        napi_value b;
        if (napi_get_element(env, args[0], i, &b) != napi_ok ||
            !get_bounds6(env, b, s->bounds + (size_t)i * 6u)) {
            free(s->bounds);
            free(s);
            return NULL;
        }
    }
    napi_create_reference(env, args[1], 1, &s->callback);
    s->scene = lrt_scene_create(s->nprims, node_lrt_bounds, node_lrt_intersect, s);
    if (!s->scene) {
        scene_finalize(env, s, NULL);
        napi_throw_error(env, NULL, "lrt_scene_create failed");
        return NULL;
    }
    if (napi_wrap(env, thisv, s, scene_finalize, NULL, &s->wrapper) != napi_ok) {
        scene_finalize(env, s, NULL);
        napi_throw_error(env, NULL, "napi_wrap failed");
        return NULL;
    }
    return thisv;
}

static node_scene *unwrap_scene(napi_env env, napi_callback_info info, napi_value *this_out) {
    napi_value thisv;
    size_t argc = 0;
    napi_get_cb_info(env, info, &argc, NULL, &thisv, NULL);
    node_scene *s = NULL;
    if (napi_unwrap(env, thisv, (void **)&s) != napi_ok || !s) {
        napi_throw_type_error(env, NULL, "invalid Scene");
        return NULL;
    }
    if (this_out) *this_out = thisv;
    return s;
}

static napi_value Scene_build(napi_env env, napi_callback_info info) {
    node_scene *s = unwrap_scene(env, info, NULL);
    if (!s) return NULL;
    if (!lrt_scene_build(s->scene)) {
        napi_throw_error(env, NULL, lrt_scene_last_error(s->scene));
        return NULL;
    }
    napi_value undef;
    napi_get_undefined(env, &undef);
    return undef;
}

static napi_value Scene_intersect(napi_env env, napi_callback_info info) {
    napi_value thisv;
    node_scene *s = unwrap_scene(env, info, &thisv);
    (void)thisv;
    if (!s) return NULL;
    size_t argc = 4;
    napi_value args[4];
    napi_get_cb_info(env, info, &argc, args, NULL, NULL);
    if (argc < 2) {
        napi_throw_type_error(env, NULL, "intersect(org, dir, tmin=0, tmax=Infinity)");
        return NULL;
    }
    double org[3], dir[3];
    if (!get_float3(env, args[0], org) || !get_float3(env, args[1], dir)) return NULL;
    double tmin = 0.0;
    double tmax = DBL_MAX;
    if (argc > 2) napi_get_value_double(env, args[2], &tmin);
    if (argc > 3) napi_get_value_double(env, args[3], &tmax);
    s->callback_failed = 0;
    double t = 0.0, u = 0.0, v = 0.0;
    unsigned prim = lrt_scene_intersect(s->scene, org, dir, tmin, tmax, &t, &u, &v);
    if (s->callback_failed) return NULL;
    if (prim == LRT_NO_HIT) {
        if (lrt_scene_last_result(s->scene) != LRT_RESULT_OK) {
            napi_throw_error(env, NULL, lrt_scene_last_error(s->scene));
            return NULL;
        }
        napi_value nullv;
        napi_get_null(env, &nullv);
        return nullv;
    }
    napi_value out, item;
    napi_create_array_with_length(env, 4, &out);
    napi_create_uint32(env, prim, &item);
    napi_set_element(env, out, 0, item);
    napi_create_double(env, t, &item);
    napi_set_element(env, out, 1, item);
    napi_create_double(env, u, &item);
    napi_set_element(env, out, 2, item);
    napi_create_double(env, v, &item);
    napi_set_element(env, out, 3, item);
    return out;
}

static napi_value backend_name(napi_env env, napi_callback_info info) {
    (void)info;
    napi_value s;
    napi_create_string_utf8(env, lrt_backend_name(), NAPI_AUTO_LENGTH, &s);
    return s;
}

static napi_value init(napi_env env, napi_value exports) {
    napi_property_descriptor methods[] = {
        {"build", NULL, Scene_build, NULL, NULL, NULL, napi_default, NULL},
        {"intersect", NULL, Scene_intersect, NULL, NULL, NULL, napi_default, NULL},
    };
    napi_value ctor;
    throw_status(env, napi_define_class(env, "Scene", NAPI_AUTO_LENGTH, Scene_new,
                                        NULL, 2, methods, &ctor),
                 "failed to define Scene");
    napi_create_reference(env, ctor, 1, &g_scene_ctor);
    napi_set_named_property(env, exports, "Scene", ctor);

    napi_value fn;
    napi_create_function(env, "backendName", NAPI_AUTO_LENGTH, backend_name, NULL, &fn);
    napi_set_named_property(env, exports, "backendName", fn);
    napi_value no_hit;
    napi_create_uint32(env, LRT_NO_HIT, &no_hit);
    napi_set_named_property(env, exports, "NO_HIT", no_hit);
    return exports;
}

NAPI_MODULE(NODE_GYP_MODULE_NAME, init)

