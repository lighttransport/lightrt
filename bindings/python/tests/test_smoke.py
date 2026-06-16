import lightrt_c


BOUNDS = [
    [-1.0, -1.0, -1.0, 1.0, 1.0, 1.0],
    [3.0, -1.0, -1.0, 5.0, 1.0, 1.0],
]


def box_intersect(org, direction, tmin, tmax, prim):
    lo = BOUNDS[prim][:3]
    hi = BOUNDS[prim][3:]
    near = tmin
    far = tmax
    for axis in range(3):
        d = direction[axis]
        if d == 0.0:
            if org[axis] < lo[axis] or org[axis] > hi[axis]:
                return None
            continue
        inv = 1.0 / d
        t0 = (lo[axis] - org[axis]) * inv
        t1 = (hi[axis] - org[axis]) * inv
        if t0 > t1:
            t0, t1 = t1, t0
        near = max(near, t0)
        far = min(far, t1)
        if far < near:
            return None
    return (near, 0.0, 0.0)


def test_scene_intersect():
    scene = lightrt_c.Scene(BOUNDS, box_intersect)
    scene.build()
    assert scene.intersect([0, 0, -5], [0, 0, 1])[:2] == (0, 4.0)
    assert scene.intersect([4, 0, -5], [0, 0, 1])[:2] == (1, 4.0)
    assert scene.intersect([10, 0, -5], [0, 0, 1]) is None
    assert "C11" in lightrt_c.backend_name()


if __name__ == "__main__":
    test_scene_intersect()

