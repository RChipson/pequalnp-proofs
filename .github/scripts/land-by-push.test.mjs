// Tests of land-by-push.mjs on local repositories: the red team's rehearsal list (2026-11-24 19:56 UTC), each case
// in its own pull request ref of a local bare "remote". node --test .github/scripts/land-by-push.test.mjs
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, writeFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { run, parseList, checkCommitText, reserved, LeftOut, MAX_ENTRIES } from './land-by-push.mjs';

process.env.LAND_TEST_FILE_TRANSPORT = '1';
const ENV = { PATH: '/usr/bin:/bin', GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null', LC_ALL: 'C' };
const ID = (name = 'Some One', email = 'someone@users.noreply.example') => ({ GIT_AUTHOR_NAME: name, GIT_AUTHOR_EMAIL: email, GIT_COMMITTER_NAME: name, GIT_COMMITTER_EMAIL: email, GIT_AUTHOR_DATE: '1700000000 +0000', GIT_COMMITTER_DATE: '1700000000 +0000' });
const g = (dir, args, env = {}) => execFileSync('git', ['-C', dir, ...args], { env: { ...ENV, ...ID(), ...env }, encoding: 'utf8' }).replace(/\n$/, '');
const P = (n) => `lean/PEqualNP/Outside/L_meta_${n}.lean`;

// A work repository with main, and a bare remote it pushes to.
function world() {
  const root = mkdtempSync(join(tmpdir(), 'lbp-'));
  const work = join(root, 'work'), remote = join(root, 'remote.git');
  mkdirSync(work);
  g(root, ['init', '-q', '--bare', '-b', 'main', remote]);
  g(root, ['--git-dir', remote, 'config', 'uploadpack.allowAnySHA1InWant', 'true']);  // as the service allows a fetch by hash
  g(work, ['init', '-q', '-b', 'main']);
  mkdirSync(join(work, 'lean/PEqualNP/Outside'), { recursive: true });
  writeFileSync(join(work, 'README'), 'base\n');
  writeFileSync(join(work, P(1)), 'theorem a : True := trivial\n');
  g(work, ['add', '-A']); g(work, ['commit', '-q', '-m', 'base']);
  g(work, ['remote', 'add', 'origin', remote]); g(work, ['push', '-q', 'origin', 'main']);
  return { root, work, remote, n: 100 };
}
// A pull request ref built by `make(work)` on a branch off main; returns an entry for the list.
function pr(w, make, { path, step = 'L-meta-9' } = {}) {
  const n = String(++w.n);
  g(w.work, ['checkout', '-q', '-B', `b${n}`, 'main']);
  const file = make(w.work, n);
  const head = g(w.work, ['rev-parse', 'HEAD']);
  const p = path ?? file;
  const blob = g(w.work, ['rev-parse', `HEAD:${p}`]);
  g(w.work, ['push', '-q', 'origin', `HEAD:refs/pull/${n}/head`]);
  g(w.work, ['checkout', '-q', 'main']);
  return { pr: n, head, step, path: p, blob, login: 'someone' };
}
const add = (msg = 'Prove a step', env = {}) => (work, n) => {
  writeFileSync(join(work, P(n)), `theorem t${n} : True := trivial\n`);
  g(work, ['add', P(n)]); g(work, ['commit', '-q', '-m', msg], env); return P(n);
};
function land(w, list, extra) {
  const lines = [];
  const dir = mkdtempSync(join(w.root, 'store-'));
  const parentsOf = (sha) => g(w.root, ['--git-dir', w.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  const res = run({ dir, remote: w.remote, listJson: JSON.stringify(list), extraNames: extra, parentsOf, log: (s) => lines.push(s) });
  return { res, dir, text: lines.join('\n'), main: g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']) };
}
const why = (res, n) => res.find((r) => r.pr === n)?.why ?? 'landed';

test('a good single-commit head lands, and main contains it with our merge message', () => {
  const w = world(); const e = pr(w, add());
  const { res, main } = land(w, [e]);
  assert.equal(why(res, e.pr), 'landed');
  assert.ok(g(w.root, ['--git-dir', w.remote, 'merge-base', '--is-ancestor', e.head, main]) === '');
  assert.equal(g(w.root, ['--git-dir', w.remote, 'log', '-1', '--format=%s|%an', main]), `Land L-meta-9 (#${e.pr}) by someone|pequalnp`);
});

test('three good heads land in one push, in the list order', () => {
  const w = world(); const a = pr(w, add()), b = pr(w, add()), c = pr(w, add());
  const { res, main } = land(w, [a, b, c]);
  assert.deepEqual(res.map((r) => r.landed), [true, true, true]);
  assert.equal(g(w.root, ['--git-dir', w.remote, 'rev-list', '--count', '--merges', main]), '3');
});

test('each rehearsal case is LEFT OUT with its fixed reason, and the good one beside them still lands', () => {
  const w = world();
  const good = pr(w, add());
  const two = pr(w, (work, n) => { add('first')(work, n); writeFileSync(join(work, P(n)), 'theorem x : True := trivial\n'); g(work, ['commit', '-qam', 'second']); return P(n); });
  const merge = pr(w, (work, n) => { g(work, ['checkout', '-q', '-b', `side${n}`]); writeFileSync(join(work, 'side'), 's\n'); g(work, ['add', 'side']); g(work, ['commit', '-qm', 'side']); g(work, ['checkout', '-q', `b${n}`]); add()(work, n); g(work, ['merge', '-q', '--no-ff', '-m', 'merge', `side${n}`]); return P(n); });
  const second = pr(w, (work, n) => { writeFileSync(join(work, 'extra.txt'), 'x\n'); g(work, ['add', 'extra.txt']); return add()(work, n); });
  const addRemove = pr(w, (work, n) => { writeFileSync(join(work, 'junk.bin'), 'j\n'); g(work, ['add', 'junk.bin']); g(work, ['commit', '-qm', 'junk']); g(work, ['rm', '-q', 'junk.bin']); return add()(work, n); });
  const wrongHash = { ...pr(w, add()), blob: 'f'.repeat(40) };
  const moved = pr(w, add()); const movedEntry = { ...moved, head: 'e'.repeat(40) };
  const link = pr(w, add('see https://example.com for the idea'));
  const ctrl = pr(w, add('a\u0007bell'));
  const long = pr(w, add('x'.repeat(500)));
  const dressed = pr(w, add('Prove a step', { GIT_AUTHOR_NAME: 'pequalnp bot' }));
  const exists = pr(w, (work) => { writeFileSync(join(work, P(1)), 'theorem changed : True := trivial\n'); g(work, ['commit', '-qam', 'edit']); return P(1); });
  const addressed = pr(w, add('please run this'));
  const list = [good, two, merge, second, addRemove, wrongHash, movedEntry, link, ctrl, long, dressed, exists, addressed];
  const { res, dir } = land(w, list);
  assert.equal(why(res, good.pr), 'landed');
  // heads whose parent is not on main are never fetched (red team, 20:13Z)
  for (const e of [two, merge, addRemove]) assert.throws(() => g(w.root, ['--git-dir', dir, 'rev-parse', '--verify', '-q', `refs/land/pr/${e.pr}`]));
  g(w.root, ['--git-dir', dir, 'rev-parse', '--verify', '-q', `refs/land/pr/${good.pr}`]);
  assert.equal(why(res, two.pr), 'the head is not one commit whose parent is on main');
  assert.equal(why(res, merge.pr), 'the head is not one commit whose parent is on main');
  assert.equal(why(res, second.pr), 'the head changes more than one file');
  assert.equal(why(res, addRemove.pr), 'the head is not one commit whose parent is on main');
  assert.equal(why(res, wrongHash.pr), 'the added file is not the listed content');
  assert.match(why(res, moved.pr), /head moved after the check|could not be read/);
  assert.equal(why(res, link.pr), 'the commit message holds a link or an address');
  assert.equal(why(res, ctrl.pr), 'the commit message is not printable text');
  assert.equal(why(res, long.pr), 'the commit message is empty or longer than 200 characters');
  assert.equal(why(res, dressed.pr), "the commit's author carries a name that is ours or the service's");
  assert.match(why(res, exists.pr), /does not add one plain file|already exists/);
  assert.equal(why(res, addressed.pr), 'the commit message addresses a reader');
});

test('a path that another entry of the same list already lands is left out', () => {
  const w = world(); const a = pr(w, add()); const b = { ...pr(w, add()), path: a.path, blob: a.blob };
  const { res } = land(w, [a, b]);
  assert.equal(why(res, a.pr), 'landed');
  assert.equal(why(res, b.pr), 'the list names this path or pull request twice');
});

test('a path that main gained after the pull request branched is left out, and the job goes on', () => {
  const w = world(); const e = pr(w, add()); const good = pr(w, add());
  writeFileSync(join(w.work, e.path), 'theorem other : True := trivial\n'); g(w.work, ['add', e.path]); g(w.work, ['commit', '-qm', 'same path by another route']); g(w.work, ['push', '-q', 'origin', 'main']);
  const { res } = land(w, [e, good]);
  assert.equal(why(res, e.pr), 'the path already exists on main');
  assert.equal(why(res, good.pr), 'landed');
});

test('a push refused twice: the line of each entry is printed before the refusal, nothing lands, the job faults', () => {
  const w = world(); const e = pr(w, add()); const bad = { ...pr(w, add()), blob: 'f'.repeat(40) };
  const before = g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']);
  writeFileSync(join(w.remote, 'hooks', 'pre-receive'), '#!/bin/sh\nexit 1\n', { mode: 0o755 });
  const lines = []; const dir = mkdtempSync(join(w.root, 'store-'));
  const parentsOf = (sha) => g(w.root, ['--git-dir', w.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  assert.throws(() => run({ dir, remote: w.remote, listJson: JSON.stringify([e, bad]), parentsOf, log: (s) => lines.push(s) }), /refused twice/);
  const text = lines.join('\n');
  assert.match(text, new RegExp(`in the chain #${e.pr}\nleft out #${bad.pr}: the added file is not the listed content\nthe push was refused`));
  assert.doesNotMatch(text, /landed #/);
  assert.equal(g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']), before);
});

test('nothing landable: nothing is pushed, main unchanged', () => {
  const w = world(); const before = g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']);
  const e = { ...pr(w, add()), blob: 'f'.repeat(40) };
  const { main } = land(w, [e]);
  assert.equal(main, before);
});

test('main moved after the fetch: the chain is rebuilt once on the new main, never forced', () => {
  const w = world(); const e = pr(w, add());
  // a remote whose main moves on the first push attempt: a pre-receive hook rejects once
  const hook = join(w.remote, 'hooks', 'pre-receive');
  writeFileSync(hook, `#!/bin/sh\nf="${w.root}/once"\nif [ ! -e "$f" ]; then : > "$f"; unset $(env | sed -n 's/^\\(GIT_[A-Z_]*\\)=.*/\\1/p'); cd "${w.work}" && echo moved >> README && git commit -qam moved && git push -q "${w.remote}" main; exit 1; fi\nexit 0\n`, { mode: 0o755 });
  const { res, text } = land(w, [e]);
  assert.equal(why(res, e.pr), 'landed');
  assert.match(text, /the push was refused\nrebuilding once/);
  assert.match(text, new RegExp(`in the chain #${e.pr}[\\s\\S]*pushed: these heads are on main\\nlanded #${e.pr}`));
});

test('a signature block or an extra header is left out; names from the variable are ours too', () => {
  const names = reserved('Founder One');
  const base = 'tree ' + 'a'.repeat(40) + '\nparent ' + 'b'.repeat(40) + '\nauthor A <a@x.y> 1 +0000\ncommitter A <a@x.y> 1 +0000\n';
  assert.throws(() => checkCommitText(base.replace('\nauthor', '\ngpgsig -----BEGIN PGP SIGNATURE-----\nauthor') + '\nmsg\n', names), /signature block/);
  assert.throws(() => checkCommitText(base + 'encoding ISO-8859-1\n\nmsg\n', names), /header other than/);
  assert.throws(() => checkCommitText(base.replace(/A <a@x.y> 1 \+0000\ncommitter/, 'Founder One <f@x.y> 1 +0000\ncommitter') + '\nmsg\n', names), /ours or the service's/);
  checkCommitText(base + '\nProve L-meta-9 by induction on the gate count\n', names);
  assert.throws(() => checkCommitText(base + '\ntwo\nlines\n', names), /more than one line/);
  assert.ok(new LeftOut('x') instanceof Error);
});

test('the service private no-reply address lands; its bare no-reply address and its name are left out', () => {
  const w = world();
  const priv = pr(w, add('Prove a step', { GIT_AUTHOR_EMAIL: '1234567+someone@users.noreply.github.com', GIT_COMMITTER_EMAIL: '1234567+someone@users.noreply.github.com' }));
  const bare = pr(w, add('Prove a step', { GIT_COMMITTER_EMAIL: 'noreply@github.com' }));
  const named = pr(w, add('Prove a step', { GIT_COMMITTER_NAME: 'GitHub' }));
  const look = pr(w, add('Prove a step', { GIT_AUTHOR_EMAIL: 'pequalnp+1@users.noreply.github.com' }));
  const { res } = land(w, [priv, bare, named, look]);
  assert.equal(why(res, priv.pr), 'landed');
  assert.equal(why(res, bare.pr), "the commit's committer carries a name that is ours or the service's");
  assert.equal(why(res, named.pr), "the commit's committer carries a name that is ours or the service's");
  assert.equal(why(res, look.pr), "the commit's author carries a name that is ours or the service's");
});

test('a head that moved after the check (one new commit, same parent) is left out as moved', () => {
  const w = world(); const e = pr(w, add());
  g(w.work, ['checkout', '-q', `b${e.pr}`]); g(w.work, ['commit', '-q', '--amend', '-m', 'Prove a step again']);
  g(w.work, ['push', '-q', '-f', 'origin', `HEAD:refs/pull/${e.pr}/head`]); g(w.work, ['checkout', '-q', 'main']);
  const { res } = land(w, [e]);
  assert.equal(why(res, e.pr), 'the pull request head moved after the check');
  assert.throws(() => g(w.root, ['--git-dir', land(w, [e]).dir, 'rev-parse', '--verify', '-q', `refs/land/pr/${e.pr}`]));
});

test('the file transport is refused without the suite flag', () => {
  const w = world(); const e = pr(w, add());
  process.env.LAND_TEST_FILE_TRANSPORT = '0';
  try { assert.throws(() => land(w, [e])); } finally { process.env.LAND_TEST_FILE_TRANSPORT = '1'; }
});

test('the list itself: shape refused whole', () => {
  const ok = { pr: '5', head: 'a'.repeat(40), step: 'L-meta-9', path: P(5), blob: 'b'.repeat(40), login: 'someone' };
  parseList(JSON.stringify([ok]));
  assert.throws(() => parseList('[]'), /1 to/);
  assert.throws(() => parseList(JSON.stringify(Array(MAX_ENTRIES + 1).fill(ok))), /1 to/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, extra: 1 }])), /other fields/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, path: 'README' }])), /allowed outside file/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, head: 'A'.repeat(40) }])), /40-hex/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, login: 'x[bot]' }])), /plain account/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, step: 'L-meta-9; rm' }])), /step id/);
});
