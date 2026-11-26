#!/usr/bin/env python3
"""Use the time a promise "find" row is held for the full search: every circuit of exactly bar - 1 and exactly
bar gates (which covers every smaller size, by a doubled NOT).  If one is found it is sent under the live lease;
if both searches end without one, the row is handed back as statement_seems_false; if the time runs out,
nothing is done (the renewal job hands the row back as usual).

  python3 generator/promise/deep.py <step id> <seconds>"""
import json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mux'))
import genprom, unread
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
step, secs = sys.argv[1], float(sys.argv[2])
def log(*a): print(time.strftime('%H:%M:%S', time.gmtime()), step, *a, flush=True)
if len(sys.argv) > 3:                      # child: one exact size
    n, mask, k = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    g = genprom.circuit(n, mask, k); print('GATES' + repr(g)); sys.exit(0)
lf = f'.pnp/{step}.json'
stmt = json.load(open(lf))['gap']['statement'].strip()
n, mask, bar = genprom.parse(' '.join(stmt.split()))
t_end = time.time() + secs; gates = None; exhausted = True
for k in (bar - 1, bar):
    left = t_end - time.time()
    if left < 5: exhausted = False; break
    try: o = subprocess.run([sys.executable, os.path.abspath(__file__), step, '0', str(n), str(mask), str(k)], capture_output=True, text=True, timeout=left).stdout
    except subprocess.TimeoutExpired: exhausted = False; log('exactly', k, 'gates: not finished'); break
    if o.startswith('GATES['): gates = eval(o[5:]); break
    log('exactly', k, 'gates: none')
if not os.path.exists(lf): log('the lease is gone; nothing done'); sys.exit(0)
if gates and unread.check(n, mask, gates):
    out = f'{S}/desk/unread/{step.replace("-", "_")}.lean'; open(out, 'w').write(genprom.lean(step, stmt, n, gates))
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 900 lake env lean {out}', shell=True, capture_output=True, text=True, env=ENV)
    if c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr):
        s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=ENV)
        log('SENT:', len(gates), 'gates |', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
    else: log('a circuit was found but the proof does not compile')
elif exhausted:
    r = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'statement_seems_false'], capture_output=True, text=True)
    log('no circuit of at most', bar, 'gates exists (exhaustive search); handed back as statement_seems_false |', r.stdout.strip()[:70])
else: log('undecided when the time ran out')
