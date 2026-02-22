@vertex
fn vs_main(@location(0) pos: vec3f) -> @builtin(position) vec4f {
    return vec4f(pos, 1.0);
}

@fragment
fn fs_main() -> @location(0) vec4f {
    return vec4f(0.0, 0.6, 1.0, 1.0);
}
