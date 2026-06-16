const mod = await import('../dist/lightrt.js');
console.log('mod.default callable:', typeof mod.default);

if (typeof mod.default === 'function') {
  console.log('Calling mod.default()...');
  const lightrt = await mod.default();
  console.log('TriangleBVH:', typeof lightrt.TriangleBVH);
  console.log('Ray:', typeof lightrt.Ray);
  console.log('Vec3:', typeof lightrt.Vec3);
} else {
  console.log('mod.default is not a function');
  console.log('Type:', typeof mod.default);
}
