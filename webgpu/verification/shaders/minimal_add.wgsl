@group(0) @binding(0)
var<storage, read> in_a : array<u32>;

@group(0) @binding(1)
var<storage, read> in_b : array<u32>;

@group(0) @binding(2)
var<storage, read_write> out_c : array<u32>;

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(local_invocation_index) idx : u32) {
  out_c[idx] = in_a[idx] + in_b[idx];
}
