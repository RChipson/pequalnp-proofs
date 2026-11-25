"""By-the-book desk client (the steps of https://pequalnp.com/join.txt done by hand, because
this session has no signed-in `gh` for the upstream repository).

  python3 generator/desk.py next [--another] [--hard] [--level warmup|solid|hard|open]
                                 [--kind prove|refute|search|cut] [--proof-of <step>]
                                                         take a step with a lease; print it
                                                         (--proof-of: lease a step we already hold a
                                                         compiled proof of, as join.txt allows)
  python3 generator/desk.py beat                         renew every lease we hold
  python3 generator/desk.py held                         list the leases we hold
  python3 generator/desk.py release <step> <reason>      give a step back with an honest reason
  python3 generator/desk.py submitted <step>             tell the desk the pull request is open

State is kept as the project's own script keeps it: .pnp/<step>.json while held, moved to
.pnp/done/ when released.  One request at a time; nothing is sent but the handle and lease."""
import json, os, re, subprocess, sys, time

DESK = 'https://pequalnp.com/desk'
HANDLE = 'RChipson'
STATE = '.pnp'

def call(method, path):
    cmd = ['curl', '-sS', '-m', '30', '-w', '\n%{http_code}', '-X', method, DESK + path]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    body, _, code = out.rpartition('\n')
    return int(code or 0), body

def held():
    return sorted(f[:-5] for f in os.listdir(STATE) if f.endswith('.json') and not f.startswith('.'))

def load(step):
    return json.load(open(f'{STATE}/{step}.json'))

def finish(step):
    os.makedirs(f'{STATE}/done', exist_ok=True)
    os.replace(f'{STATE}/{step}.json', f'{STATE}/done/{step}.json')

def stop_notice():
    # The project's stop notice: a file STOP at the root of its main branch stops all desk work.
    subprocess.run(['git', 'fetch', '-q', 'upstream', 'main'], capture_output=True, timeout=60)
    r = subprocess.run(['git', 'cat-file', '-e', 'upstream/main:STOP'], capture_output=True)
    if r.returncode == 0:
        line = subprocess.run(['git', 'cat-file', 'blob', 'upstream/main:STOP'], capture_output=True, text=True).stdout.split('\n')[0]
        print('STOPPED by a notice on the proofs repository:', re.sub(r"[^A-Za-z0-9 .,:;()'-]", '', line)[:200])
        return True
    return False

def opt(name, pattern):
    if name in sys.argv:
        v = sys.argv[sys.argv.index(name) + 1]
        assert re.fullmatch(pattern, v), f'{name} needs a value like {pattern}'
        return v
    return None

def main():
    os.makedirs(STATE, exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'held'
    if cmd in ('next', 'beat'):
        try:
            if stop_notice(): return 120
        except Exception as e:
            print('note: the stop notice could not be read; going on')
    if cmd == 'next':
        q = f'handle={HANDLE}'
        if '--another' in sys.argv: q += '&another=1'
        if '--hard' in sys.argv: q += '&hard=1'
        for name in ('--level', '--kind'):
            v = opt(name, r'[a-z]{1,10}')
            if v: q += f'&{name[2:]}={v}'
        v = opt('--proof-of', r'L-[a-z]+-[0-9]+')
        if v: q += f'&gap={v}&have=proof'
        code, body = call('GET', '/next?' + q)
        if code != 200:
            print('desk answered', code, body[:300]); return 1
        d = json.loads(body)
        g = d.get('gap')
        if not g:
            print(d.get('note') or d.get('error') or 'no step right now'); return 0
        gid = g['id']
        assert re.fullmatch(r'L-[a-z]+-\d+', gid)
        # the lease is recorded first, so that a step is never held without a record of it
        json.dump(d, open(f'{STATE}/{gid}.json', 'w'), indent=1)
        path, module = g.get('file'), g.get('module')
        print('STEP   ', gid, '| weight', g.get('weight'), '|', g.get('title', '')[:160])
        print('FILE   ', path, '| module', module, '| imports', g.get('imports'))
        print('LEASE  ', d['lease']['id'], 'until', d['lease']['expires_at'])
        t = d['lease'].get('terms') or {}
        if t: print('TERMS  ', t.get('level'), t.get('kind'), '|', t.get('points'), 'points', '| racing another holder' if t.get('race') else '')
        if d.get('task'): print('TASK   ', d.get('task'), json.dumps(d.get('direction'))[:600])
        for k in ('shard', 'shards'):
            if k in d: print(k.upper() + ':', d[k])
        if g.get('shard_spec'): print('SHARD_SPEC:', str(g['shard_spec'])[:900])
        if not path or not re.fullmatch(r'lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean', path):
            print('NOTE: this step has no ordinary file (a value step or malformed); look at', f'{STATE}/{gid}.json')
        for k in ('unlocks', 'context', 'sketch', 'refutation'):
            if g.get(k): print(k.upper() + ':', (g[k] if isinstance(g[k], str) else json.dumps(g[k]))[:900])
        for x in g.get('dead') or []: print('FAILED:', str(x)[:300])
        print('STATEMENT:', g.get('statement'))
        return 0
    if cmd == 'beat':
        for step in held():
            code, body = call('POST', '/beat?lease=' + load(step)['lease']['id'])
            if code == 410:
                print(step, 'STOP 410: settled by someone else or withdrawn; stop work on it'); finish(step)
            elif code == 200:
                print(step, 'lease until', json.loads(body)['lease']['expires_at'])
            else:
                print(step, 'beat answered', code, body[:200])
            time.sleep(3)
        return 0
    if cmd == 'held':
        for step in held():
            d = load(step); print(step, d['gap']['file'], 'lease', d['lease']['id'])
        return 0
    if cmd in ('release', 'submitted'):
        step = sys.argv[2]
        reason = 'submitted' if cmd == 'submitted' else sys.argv[3]
        code, body = call('POST', f"/release?lease={load(step)['lease']['id']}&reason={reason}")
        print(step, 'release', reason, '->', code, body[:200].replace('\n', ' '))
        if code in (200, 410): finish(step)
        return 0
    print(__doc__); return 1

if __name__ == '__main__':
    sys.exit(main())
