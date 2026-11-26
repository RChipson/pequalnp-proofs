#!/usr/bin/env python3
"""Automatic responder: watch the desk's list and, for a newly posted row of a family we can settle in a
minute or two, write the proof, compile it, ask the desk for the step with --proof-of and submit.

Families (each handler returns the path of a Lean file that compiled, or None):
  gift      the row's notes spell out a gate list ("OR 0 1, AND 5 10, ...; output wire 16"): the proof is that
            circuit, replayed by the kernel.
  find      "an AND/OR/NOT circuit of at most k gates represents the graph with mask M on the promise": SAT
            search for the circuit (generator/promise/genprom.py, xorsynth.py).
  floor     "no AND/OR/NOT circuit of at most k gates represents ...": the free-NOT sample search
            (generator/promise/gennone.py) or a solver certificate (generator/lratfloor/mkfloor.py).

  python3 generator/respond/auto_respond.py <minutes> [dry]
dry: build and compile, but do not ask the desk or submit.  Rows already listed at start-up are not touched."""
import fcntl, json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); GEN = os.path.join(HERE, '..')
sys.path.insert(0, os.path.join(GEN, 'promise')); sys.path.insert(0, os.path.join(GEN, 'mux'))
import genprom, unread
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
D = f'{S}/desk/respond'; os.makedirs(D, exist_ok=True)
P = 'PEqualNP.CircuitLowerBounds'
def log(*a): print(time.strftime('%H:%M:%S', time.gmtime()), *a, flush=True)
def gaps():
    raw = subprocess.run(['curl', '-s', '-m', '40', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    return {g['id']: g for g in json.loads(raw)['gaps']}
def is_open(g): return g is not None and str(g.get('pr_open', '0')) in ('0', 'None')
def num(i):
    m = re.match(r'L-[a-z]+-(\d+)$', i); return int(m.group(1)) if m else -1
def compiles(path):
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 900 lake env lean {path}', shell=True, capture_output=True, text=True, env=ENV)
    return c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr)

def witness_lean(step, stmt, gates, outw):
    """gates: list of (op, [wires]); a witness proof for '∃ C, FanInTwo/Monotone2 C ∧ C.size ≤ k ∧ ...' or RepSizeAtMost"""
    tag = step.replace('-', '_'); ns = f'PEqualNP.Outside.{tag}_aux'
    gl = ', '.join(f'⟨{P}.GateOp.{op}, [{", ".join(map(str, ins))}]⟩' for op, ins in gates)
    rf = ' | '.join(['rfl'] * len(gates))
    return f'''import Mathlib
import PEqualNP.Defs

namespace {ns}

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : {P}.Circuit := ⟨[{gl}], {outw}⟩

end {ns}

theorem PEqualNP.Outside.{tag} : {stmt} := by
  refine ⟨{ns}.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [{ns}.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {rf} <;> simp
  · decide
  · decide +kernel
'''

GATES = re.compile(r'((?:OR|AND|NOT) \d+(?: \d+)?(?:, (?:OR|AND|NOT) \d+(?: \d+)?)+)[;.,]? ?(?:the )?output(?: is)?(?: wire)? (\d+)')
def h_gift(step, g, stmt):
    if not (stmt.startswith('∃ C : PEqualNP.CircuitLowerBounds.Circuit,') or stmt.startswith('PEqualNP.Represents.RepSizeAtMost')): return None
    m = GATES.search(g.get('sketch', '') + ' ' + g.get('context', ''))
    if not m: return None
    gates = []
    for t in m.group(1).split(', '):
        p = t.split(); gates.append((p[0].lower(), [int(x) for x in p[1:]]))
    out = f'{D}/{step.replace("-", "_")}.lean'
    open(out, 'w').write(witness_lean(step, stmt, gates, int(m.group(2))))
    return out if compiles(out) else None

def h_find(step, g, stmt):
    p = genprom.parse(' '.join(stmt.split()))
    if not p: return None
    n, mask, bar = p
    code = '''
import sys
sys.path.insert(0, %r); sys.path.insert(0, %r)
import genprom, unread, xorsynth
n, mask, bar = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
for k in range(1, min(bar, 7) + 1):
    c = genprom.circuit(n, mask, k)
    if c: print(repr(c)); sys.exit(0)
if bar >= 8:
    c = xorsynth.find(n, mask, bar, 150)
    if c: print(repr(c)); sys.exit(0)
print('None')
''' % (os.path.join(GEN, 'promise'), os.path.join(GEN, 'mux'))
    try: o = subprocess.run(['python3', '-c', code, str(n), str(mask), str(bar)], capture_output=True, text=True, timeout=240).stdout.strip()
    except subprocess.TimeoutExpired: return None
    if not o.startswith('['): return None
    gates = eval(o)
    if not unread.check(n, mask, gates): return None
    out = f'{D}/{step.replace("-", "_")}.lean'
    open(out, 'w').write(genprom.lean(step, stmt, n, gates))
    return out if compiles(out) else None

def h_floor(step, g, stmt):
    if not ' '.join(stmt.split()).startswith('¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤'): return None
    sf = f'{D}/stmt_{step}.txt'; open(sf, 'w').write(stmt); out = f'{D}/{step.replace("-", "_")}.lean'
    try:
        r = subprocess.run(['python3', os.path.join(GEN, 'promise', 'gennone.py'), step, sf, out], capture_output=True, text=True, timeout=200)
        if r.returncode == 0 and compiles(out): return out
    except subprocess.TimeoutExpired: pass
    if not any(i.endswith('LRAT.PromiseN') for i in g.get('imports', [])): return None
    try: r = subprocess.run(['python3', os.path.join(GEN, 'lratfloor', 'mkfloor.py'), step, sf, out, '240'], capture_output=True, text=True, timeout=400)
    except subprocess.TimeoutExpired: return None
    if r.returncode != 0 or os.path.getsize(out) > 500 * 1024: return None
    return out if compiles(out) else None

HANDLERS = [('gift', h_gift), ('find', h_find), ('floor', h_floor)]

def send(step, out):
    with open('/tmp/submit.lock', 'w') as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            if not is_open(gaps().get(step)): log(step, 'was taken meanwhile; proof kept at', out); return False
        except Exception: pass
        nx = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
        m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', nx.stdout, re.M)
        if not m or m.group(1) != step: log(step, 'not handed to us:', nx.stdout.strip()[:150], '| proof kept at', out); return False
        subprocess.Popen(['bash', 'generator/hold.sh', step, 'out_of_time', '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
        s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=ENV)
        log('SENT', step, (s.stdout + s.stderr).strip().split('\n')[-1][:200])
        return True

def main():
    end = time.time() + 60 * float(sys.argv[1]); dry = len(sys.argv) > 2 and sys.argv[2] == 'dry'
    G = gaps()
    seen = set(G)
    log('watching;', len(G), 'steps open; only rows posted from now on are answered')
    while time.time() < end:
        try: G = gaps()
        except Exception as e: time.sleep(20); continue
        new = sorted((i for i in G if i not in seen), key=num)
        for step in new:
            seen.add(step); g = G[step]
            if not is_open(g) or 'Not for takers' in g.get('sketch', '') or 'do not start' in g.get('sketch', ''): continue
            stmt = g.get('statement', '').strip()
            for name, h in HANDLERS:
                t = time.time()
                try: out = h(step, g, stmt)
                except Exception as e: log(step, name, 'handler error', repr(e)[:120]); out = None
                if out:
                    log(step, name, ': proof compiles after', round(time.time() - t), 's |', g.get('title', '')[:90])
                    if not dry: send(step, out)
                    break
        time.sleep(20)
    log('time is up')
if __name__ == "__main__":
    main()
