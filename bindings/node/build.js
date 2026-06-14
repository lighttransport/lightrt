const { spawnSync } = require('node:child_process');
const fs = require('node:fs');
const path = require('node:path');

const here = __dirname;
const root = path.resolve(here, '../..');
const outDir = path.join(here, 'build', 'Release');
fs.mkdirSync(outDir, { recursive: true });

const nodeRoot = path.resolve(process.execPath, '..', '..');
const includeCandidates = [
  path.join(nodeRoot, 'include', 'node'),
  '/usr/include/node',
  '/usr/include/nodejs/src',
];
const nodeInclude = includeCandidates.find((dir) =>
  fs.existsSync(path.join(dir, 'node_api.h'))
);
if (!nodeInclude) {
  throw new Error('Could not find node_api.h. Set up a Node.js install with headers.');
}

const cc = process.env.CC || 'cc';
const output = path.join(outDir, 'lightrt_c.node');
const args = [
  '-std=c11',
  '-O3',
  '-fPIC',
  '-shared',
  '-I', root,
  '-I', nodeInclude,
  path.join(here, 'src', 'lightrt_c_node.c'),
  path.join(root, 'lightrt_c.c'),
  '-lm',
  '-o', output,
];

const res = spawnSync(cc, args, { stdio: 'inherit' });
if (res.status !== 0) {
  process.exit(res.status || 1);
}

