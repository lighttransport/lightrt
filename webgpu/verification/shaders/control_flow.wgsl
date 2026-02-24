@group(0) @binding(0)
var<storage, read> in_a : array<u32>;

@group(0) @binding(1)
var<storage, read_write> out_u : array<u32>;

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(local_invocation_index) idx : u32) {
  var v = in_a[idx];
  if ((idx & 1u) == 1u) {
    v = v * 3u + 5u;
  } else {
    v = v + 11u;
  }
  out_u[idx] = v;
}
