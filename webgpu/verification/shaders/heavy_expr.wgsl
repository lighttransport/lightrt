@group(0) @binding(0)
var<storage, read> in_a : array<u32>;

@group(0) @binding(1)
var<storage, read> in_b : array<u32>;

@group(0) @binding(2)
var<storage, read_write> out_u : array<u32>;

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(local_invocation_index) idx : u32) {
  let va = in_a[idx];
  let vb = in_b[idx];
  let lane = ((idx & 1u) << 4u) + ((idx & 3u) << 2u);
  out_u[idx] = va * 3u + vb + lane;
}
