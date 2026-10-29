import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { copyFileSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const packageRoot = fileURLToPath(new URL('../', import.meta.url));
const temp = mkdtempSync(join(tmpdir(), 'suimon-package-'));
try {
  execFileSync('pnpm', ['pack', '--pack-destination', temp], { cwd: packageRoot, stdio: 'inherit' });
  const archive = readdirSync(temp).find(name => name.endsWith('.tgz'));
  assert.ok(archive, 'pack must produce a tarball');
  writeFileSync(join(temp, 'package.json'), JSON.stringify({ name: 'suimon-consumer-test', private: true, type: 'module' }));
  execFileSync('npm', ['install', '--ignore-scripts', '--no-audit', '--no-fund', join(temp, archive)], { cwd: temp, stdio: 'inherit' });
  copyFileSync(join(packageRoot, 'examples/workflow.mjs'), join(temp, 'example.mjs'));
  const output = execFileSync(process.execPath, ['example.mjs'], { cwd: temp, encoding: 'utf8' });
  assert.match(output, /succeeded/);
  assert.match(output, /HELLO/);
  assert.match(output, /SUIMON/);
  assert.equal(output.trim().split('\n').length, 2, 'run and resume each produce a result');
  writeFileSync(join(temp, 'consumer.ts'), `
    import { DefinitionBuilder, defineType, type RecoverableJournal } from '@suimon/engine';
    const text = defineType('Text', value => { if (typeof value !== 'string') throw new TypeError(); return value; });
    const d = new DefinitionBuilder();
    const f = d.func('f', text, text, (value, { signal }) => { signal.throwIfAborted(); return value; });
    const w = d.workflow('w', text);
    const end = w.call('end', f, { policy: 'stop' });
    w.entry(end);
    const engine = d.build(w);
    const report = await engine.run('input');
    const result: string = report.output(end);
    // @ts-expect-error The installed package preserves workflow input types.
    engine.run(123);
    // @ts-expect-error The installed package preserves endpoint output types.
    const wrong: number = report.output(end);
    const useJournal = (journal: RecoverableJournal) => engine.resume(journal);
    void [result, wrong, useJournal];
  `);
  execFileSync(join(packageRoot, 'node_modules/.bin/tsc'), ['--strict', '--noEmit', '--target', 'ES2023',
    '--module', 'NodeNext', '--moduleResolution', 'NodeNext', '--typeRoots', join(packageRoot, 'node_modules/@types'),
    join(temp, 'consumer.ts')], { cwd: temp, stdio: 'inherit' });
  const manifest = JSON.parse(readFileSync(join(temp, 'node_modules/@suimon/engine/package.json'), 'utf8'));
  assert.deepEqual(Object.keys(manifest.exports), ['.'], 'only the supported entry is importable');
  console.log(output.trim());
  console.log('Packed engine runs and resumes from a separate Node consumer.');
} finally {
  rmSync(temp, { recursive: true, force: true });
}
