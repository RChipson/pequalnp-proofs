#!/usr/bin/env python3
"""Search-and-send for the promise "find" rows (an AND/OR/NOT circuit of at most k gates represents the
graph with mask M on the one-a-side promise).  For every open row without a pull request: look for a
circuit that leaves the classes of equal rows / equal columns unread (unread.py), write the proof
(genprom.lean), compile it, ask the desk for the step with --proof-of and submit.

  python3 generator/promise/send_unread.py <worker index> <workers> <seconds per search> <minutes> [fast|full]\nfast: only the quick shapes of xorsynth.py; full: then the general search of unread.py as well."""
import fcntl, json, os, random, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mux'))
import genprom, unread
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
D = f'{S}/desk/unread'; os.makedirs(D, exist_ok=True)
wi, nw, secs, mins = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
def log(*a): print(time.strftime('%H:%M:%S', time.gmtime()), f'[{wi}]', *a, flush=True)
def gaps():
    raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    return {g['id']: g for g in json.loads(raw)['gaps']}
def is_open(g): return g is not None and str(g.get('pr_open', '0')) in ('0', 'None')
CODE = '''
import sys
sys.path.insert(0, %r); sys.path.insert(0, %r)
import unread, xorsynth
n, mask, k, fast = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == 'fast'
g = xorsynth.find(n, mask, k, 300)
if g and unread.check(n, mask, g): print('CIRCUIT', repr(g)); sys.exit(0)
if fast: print('none of the quick shapes'); sys.exit(0)
rc, cc = unread.classes(n, mask)
tr = [c for c in rc if len(c) > 1] or [[]]; tc = [c for c in cc if len(c) > 1] or [[]]
for sr in tr:
    for sc in tc:
        g = unread.attempt(n, mask, k, sr, sc)
        if g and unread.check(n, mask, g): print('CIRCUIT', repr(g)); sys.exit(0)
print('none')
''' % (HERE, os.path.join(HERE, '..', 'mux'))
MODE = sys.argv[5] if len(sys.argv) > 5 else 'full'
end = time.time() + 60 * mins
tried = set()
while time.time() < end:
    try: G = gaps()
    except Exception: time.sleep(20); continue
    rows = [g for g in G.values() if 'is represented on the one-a-side promise' in g.get('title', '') and is_open(g) and genprom.parse(g['statement'].strip())]
    rows = [g for g in rows if int(g['id'].split('-')[2]) % nw == wi and g['id'] not in tried and not os.path.exists(f'{D}/{g["id"]}.sent')]
    # rows with equal rows and columns first (the search is much smaller there), newest first
    def key(g):
        n, mask, bar = genprom.parse(g['statement'].strip()); rc, cc = unread.classes(n, mask)
        return (-(any(len(c) > 1 for c in rc) + any(len(c) > 1 for c in cc)), -int(g['id'].split('-')[2]))
    rows.sort(key=key)
    rows = [g for g in rows if int(g['id'].split('-')[2]) >= 19400]
    if not rows: log('nothing left for this worker'); time.sleep(60); continue
    g = rows[0]; step = g['id']; tried.add(step)
    st = g['statement'].strip(); n, mask, bar = genprom.parse(st)
    t = time.time()
    try: o = subprocess.run(['python3', '-c', CODE, str(n), str(mask), str(bar), MODE], capture_output=True, text=True, timeout=secs).stdout.strip()
    except subprocess.TimeoutExpired: o = 'timeout'
    if not o.startswith('CIRCUIT'): log(step, 'mask', mask, 'bar', bar, ':', o[:40], round(time.time() - t)); continue
    gates = eval(o[len('CIRCUIT '):])
    assert unread.check(n, mask, gates) and len(gates) <= bar
    out = f'{D}/{step.replace("-", "_")}.lean'
    open(out, 'w').write(genprom.lean(step, st, n, gates))
    log(step, 'circuit found in', round(time.time() - t), 's')
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 900 lake env lean {out}', shell=True, capture_output=True, text=True, env=ENV)
    if c.returncode or re.search(r'\berror\b', c.stdout + c.stderr): log(step, 'does not compile', (c.stdout + c.stderr)[-200:]); continue
    with open('/tmp/submit.lock', 'w') as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            if not is_open(gaps().get(step)): log(step, 'was taken meanwhile'); continue
        except Exception: pass
        nx = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
        m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', nx.stdout, re.M)
        if not m or m.group(1) != step: log(step, 'not handed to us:', nx.stdout.strip()[:150]); continue
        subprocess.Popen(['bash', 'generator/hold.sh', step, 'out_of_time', '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
        s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=ENV)
        open(f'{D}/{step}.sent', 'w').write(time.strftime('%H:%M:%S', time.gmtime()))
        log('SENT', step, (s.stdout + s.stderr).strip().split('\n')[-1][:200])
log('time is up')
