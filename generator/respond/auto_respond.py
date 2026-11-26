#!/usr/bin/env python3
"""Automatic responder: watch the desk's list and, for a newly posted row of a family we can settle in a
minute or two, write the proof, compile it, ask the desk for the step with --proof-of and submit.

Families (each handler returns the path of a Lean file that compiled, or None):
  gift      the row's notes spell out a gate list ("OR 0 1, AND 5 10, ...; output wire 16"): the proof is that
            circuit, replayed by the kernel.
  find      "an AND/OR/NOT circuit of at most k gates represents the graph with mask M on the promise": SAT
            search for the circuit (generator/promise/genprom.py, xorsynth.py).
  graph     the same kind of row for a graph given by an expression (crown, staircase, chain ...), with or
            without NOT gates: Lean prints the table, then the search runs (generator/encoder/msynth.py).
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
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1', BG_RELEASE='1')
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
    lock = 'flock /tmp/lean.lock ' if os.path.getsize(path) > 60000 else ''      # small proofs may compile side by side
    c = subprocess.run(f'cd {S}/up/lean && {lock}timeout 900 lake env lean {path}', shell=True, capture_output=True, text=True, env=ENV)
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
GATES2 = re.compile(r'((?:OR|AND|NOT)\(\d+(?:, ?\d+)?\)(?:, (?:OR|AND|NOT)\(\d+(?:, ?\d+)?\))+)')
def gift_gates(text):
    """a gate list spelled out in a unit's notes, in either of the two spellings seen: (gates, output wire or None)"""
    m = GATES.search(text)
    if m:
        gates = []
        for t in m.group(1).split(', '):
            p = t.split(); gates.append((p[0].lower(), [int(x) for x in p[1:]]))
        return gates, int(m.group(2))
    m = GATES2.search(text)
    if m:
        gates = [(op.lower(), [int(x) for x in re.findall(r'\d+', ins)]) for op, ins in re.findall(r'(OR|AND|NOT)\(([^)]*)\)', m.group(1))]
        mo = re.search(r'output(?: is)?(?: wire)? (\d+)', text[m.end():m.end() + 80])
        return gates, (int(mo.group(1)) if mo else None)
    return None
def h_gift(step, g, stmt):
    if not (stmt.startswith('∃ C : PEqualNP.CircuitLowerBounds.Circuit,') or stmt.startswith('PEqualNP.Represents.RepSizeAtMost')): return None
    gg = gift_gates(g.get('sketch', '') + ' ' + g.get('context', ''))
    if not gg: return None
    gates, outw = gg
    if outw is None:                                   # the last gate is the output; the number of inputs is not needed
        mi = re.search(r'gate k is wire (\d+) \+ k|gate j writes wire (\d+) ?\+ ?j', g.get('sketch', '') + ' ' + g.get('context', ''))
        if not mi: return None
        outw = int(mi.group(1) or mi.group(2)) + len(gates) - 1
    out = f'{D}/{step.replace("-", "_")}.lean'
    open(out, 'w').write(witness_lean(step, stmt, gates, outw))
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
if bar >= 8:
    c = xorsynth.find(n, mask, bar, 40)
    if c: print(repr(c)); sys.exit(0)
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
    flat = ' '.join(stmt.split())
    if flat.startswith('¬ ('): flat = '¬ ' + flat[3:]
    if not flat.startswith('¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤'): return None
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

REP_MONO = re.compile(r'PEqualNP\.Represents\.RepSizeAtMost \((fun u v : Fin (\d+) => .*)\) (\d+)', re.S)
REP_NOT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit,\s*PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧\s*PEqualNP\.Represents\.Represents \((fun u v : Fin (\d+) => .*)\) C', re.S)
def table_of(step, fn, n):
    """the n by n table of the posted graph expression, read off by Lean itself (a local run, not part of any proof)"""
    f = f'{D}/table_{step.replace("-", "_")}.lean'
    open(f, 'w').write(f'import Mathlib\nimport PEqualNP.Defs\n#eval (List.finRange {n}).map fun a => (List.finRange {n}).map fun b => (({fn}) a b : Bool)\n')
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 300 lake env lean {f}', shell=True, capture_output=True, text=True, env=ENV)
    m = re.search(r'\[\[.*\]\]', c.stdout, re.S)
    if c.returncode or not m: return None
    rows = [[x.strip() == 'true' for x in r.split(',')] for r in re.findall(r'\[([a-z, \n]+)\]', m.group(0))]
    return rows if len(rows) == n and all(len(r) == n for r in rows) else None

def h_graph(step, g, stmt):
    """a find row on a graph given by an expression: monotone (RepSizeAtMost) or with NOT gates"""
    m = REP_MONO.fullmatch(stmt); mono = True
    if m: fn, n, bar = m.group(1), int(m.group(2)), int(m.group(3))
    else:
        m = REP_NOT.fullmatch(stmt); mono = False
        if not m: return None
        bar, fn, n = int(m.group(1)), m.group(2), int(m.group(3))
    if n > 6 or bar > 12: return None
    T = table_of(step, fn, n)
    if T is None: return None
    mask = sum(1 << (n * u + v) for u in range(n) for v in range(n) if T[u][v])
    code = """
import sys
sys.path.insert(0, %r); sys.path.insert(0, %r); sys.path.insert(0, %r)
n, mask, bar, mono = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == '1'
if mono:
    from msynth import search
    rows = [((1 << u) | (1 << (n + v)), mask >> (n * u + v) & 1) for u in range(n) for v in range(n)]
    R = len(rows); incols = [sum(1 << r for r in range(R) if rows[r][0] >> i & 1) for i in range(2 * n)]
    target = sum(1 << r for r in range(R) if rows[r][1])
    for G in range(1, bar + 1):
        res = search(2 * n, incols, R, [target], G, 'andor', 60)
        if isinstance(res, tuple): print(repr((res[0], res[1][0]))); sys.exit(0)
        if res == 'timeout': break
else:
    import genprom
    for k in range(1, min(bar, 8) + 1):
        c = genprom.circuit(n, mask, k)
        if c: print(repr(([(t, a, b) for t, a, b in c], 2 * n + len(c) - 1))); sys.exit(0)
print('None')
""" % (os.path.join(GEN, 'promise'), os.path.join(GEN, 'mux'), os.path.join(GEN, 'encoder'))
    try: o = subprocess.run(['python3', '-c', code, str(n), str(mask), str(bar), '1' if mono else '0'], capture_output=True, text=True, timeout=200).stdout.strip()
    except subprocess.TimeoutExpired: return None
    if not o.startswith('('): return None
    gl, outw = eval(o)
    gates = [(t, [a] if t == 'not' else [a, b]) for t, a, b in gl]
    out = f'{D}/{step.replace("-", "_")}.lean'
    open(out, 'w').write(witness_lean(step, stmt, gates, outw))
    return out if compiles(out) else None


HANDLERS = [('gift', h_gift), ('find', h_find), ('floor', h_floor), ('graph', h_graph)]

RETRY = f'{D}/retry.json'
def remember(step, out, after):
    """a proof that is ready while another agent has a head start: come back when the desk said"""
    q = json.load(open(RETRY)) if os.path.exists(RETRY) else {}
    q[step] = {'out': out, 'after': after}; json.dump(q, open(RETRY, 'w'))
def retry_due(G):
    if not os.path.exists(RETRY): return
    q = json.load(open(RETRY)); now = time.strftime('%Y-%m-%dT%H:%M:%S', time.gmtime(time.time() - 3))
    for step, e in list(q.items()):
        if step not in G or not is_open(G[step]):
            del q[step]; json.dump(q, open(RETRY, 'w')); log(step, 'is closed or has a pull request; ready proof dropped'); continue
        if e['after'] > now: continue
        del q[step]; json.dump(q, open(RETRY, 'w'))
        log(step, 'head start over; bringing the ready proof back')
        send(step, e['out'])

def send(step, out):
    with open('/tmp/submit.lock', 'w') as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            if not is_open(gaps().get(step)): log(step, 'was taken meanwhile; proof kept at', out); return False
        except Exception: pass
        if os.path.exists(f'.pnp/{step}.json') or any(l.split()[:1] == [step] for l in open('generator/pr-requests.txt')):
            log(step, 'is already held or sent by us'); return False
        nx = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
        m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', nx.stdout, re.M)
        if not m or m.group(1) != step:
            mm = re.search(r'back after (\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)', nx.stdout)
            if mm: remember(step, out, mm.group(1))
            log(step, 'not handed to us:', nx.stdout.strip()[:150], '| proof kept at', out); return False
        subprocess.Popen(['bash', 'generator/hold.sh', step, 'out_of_time', '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
        s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=ENV)
        log('SENT', step, (s.stdout + s.stderr).strip().split('\n')[-1][:200])
        return True

def answer(step, g, dry):
    stmt = g.get('statement', '').strip()
    for name, h in HANDLERS:
        t = time.time()
        try: out = h(step, g, stmt)
        except Exception as e: log(step, name, 'handler error', repr(e)[:120]); out = None
        if out:
            log(step, name, ': proof compiles after', round(time.time() - t), 's |', g.get('title', '')[:90])
            if not dry: send(step, out)
            return

def main():
    from concurrent.futures import ThreadPoolExecutor
    end = time.time() + 60 * float(sys.argv[1]); dry = len(sys.argv) > 2 and sys.argv[2] == 'dry'
    G = gaps()
    seen = set(G); first = {}
    log('watching;', len(G), 'steps open; only rows posted from now on are answered')
    ex = ThreadPoolExecutor(3); busy = {}
    while time.time() < end:
        try: G = gaps()
        except Exception as e: time.sleep(20); continue
        retry_due(G)
        now = time.time()
        fresh = False
        for i in G:
            if i not in seen and i not in first: first[i] = now; fresh = True
        if fresh: open('/tmp/ask_now', 'w').write(str(now))      # tells the desk loop to ask for work now
        busy = {i: f for i, f in busy.items() if not f.done()}
        # newest rows first; a row that has waited more than 90 seconds is left alone (someone holds it by then)
        todo = sorted((i for i in first if i not in seen), key=num, reverse=True)
        for step in todo:
            g = G.get(step)
            if g is None or not is_open(g) or now - first[step] > 90 or 'Not for takers' in g.get('sketch', '') or 'do not start' in g.get('sketch', ''):
                seen.add(step); continue
            if len(busy) >= 3: break
            seen.add(step); busy[step] = ex.submit(answer, step, g, dry)
        time.sleep(8)
    log('time is up')

if __name__ == "__main__":
    main()
