#!/usr/bin/env python3
"""Rows "Table 2: for the monotone six-input f with table A * 2^32 + B: each AND/OR/NOT circuit of fan-in at most
two has an AND/OR one no larger", for the larger functions (monotone size 9 and more) that gen6.py cannot do.

The proof text is that of the merged L_meta_36404 (Ming-Chih Kao, pull request 46159, same repository,
Apache-2.0): a search over 128 pairs (false point, true point), evaluated by Lean's kernel in slices of the root's
children, shows that more than m - 2 binary gates are needed even when NOT gates are free; a monotone circuit of m
gates is the witness.  Only the data of the function changes; this program computes that data:

  witness   a monotone circuit with the fewest gates found (SAT), m gates
  pairs     every pair (true point, false point) at distance 1, then pairs at distance 2, 128 in all
  numbers   the search depth m - 3, the bound m - 2, the spare m - 7, the output wire m + 5
  slices    the root's children in slices of a fixed length (Lean computes the list itself)

  python3 gen6k.py <step id> <statement file> <out.lean> [seed] [slice length]
Exit 0: file written (whether the search really rejects is decided by Lean when the file is compiled).
Exit 1: the method does not apply (a function that ignores an input, fewer than 7 gates, no circuit found)."""
import os, random, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen6
N = 6
TEMPLATE_ID = 'L_meta_36404'
T_OLD = '4278124266 * 2 ^ 32 + 4277075656'

def template():
    return subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', f'upstream/main:lean/PEqualNP/Outside/{TEMPLATE_ID}.lean'],
                          capture_output=True, text=True, check=True).stdout

def synth(T, k, secs):
    try:
        r = subprocess.run([sys.executable, os.path.join(HERE, 'gen6.py'), 'synth', str(T), str(k)], capture_output=True, text=True, timeout=secs)
    except subprocess.TimeoutExpired:
        return 'timeout'
    return eval(r.stdout[5:]) if r.stdout.startswith('GATES') else None

def pairs_for(T, seed):
    f = lambda x: T >> x & 1
    tr = [x for x in range(64) if f(x)]; fa = [x for x in range(64) if not f(x)]
    near = [(p, q) for p in tr for q in fa if bin(p ^ q).count('1') == 1]
    far = [(p, q) for p in tr for q in fa if bin(p ^ q).count('1') == 2]
    rest = [(p, q) for p in tr for q in fa if bin(p ^ q).count('1') > 2]
    rnd = random.Random(seed); rnd.shuffle(far); rnd.shuffle(rest)
    if len(near) > 128:
        # more near pairs than places: keep for every input the pairs that differ in it, as evenly as possible
        by = {j: [pq for pq in near if pq[0] ^ pq[1] == 1 << j] for j in range(N)}
        for j in by: rnd.shuffle(by[j])
        near = []
        while len(near) < 128:
            for j in range(N):
                if by[j] and len(near) < 128: near.append(by[j].pop())
    ps = (near + far + rest)[:128]
    i = 0
    while len(ps) < 128: ps.append(ps[i]); i += 1          # a very small function: pairs repeated
    return ps, len(near)

def build(step, stmt, seed=1, slice_len=6, log=print):
    p = gen6.parse(stmt)
    if not p: return None
    expr, T = p; expr = expr[1:-1]
    f = lambda x: T >> x & 1
    for j in range(N):
        if all(f(x) == f(x ^ (1 << j)) for x in range(64)): log(f'the function ignores input {j}: not this method'); return None
    if any(f(x) and not f(x | (1 << j)) for x in range(64) for j in range(N)): log('not monotone'); return None
    gates = None
    # The fewest gates found, looking from 9 up (the functions of these batches need 9 to 12; a search that times
    # out is passed over).  If the true least size is smaller than the one used, Lean's search finds a derivation
    # and the file does not compile: nothing wrong can be sent.
    for k, secs in ((9, 30), (10, 60), (11, 90), (12, 120), (8, 30), (7, 30), (13, 120)):
        g = synth(T, k, secs)
        if g == 'timeout': log(f'the search for a circuit of {k} gates timed out'); continue
        if g and gen6.check_circuit(T, g): gates = g; break
    if not gates: log('no monotone circuit of 7 to 13 gates found (fewer than 7 gates is not this method)'); return None
    m = len(gates); n = m - 2; k = m - 3; e = m - 7; out = N + m - 1
    ps, nnear = pairs_for(T, seed)
    row = lambda j: sum((p >> j & 1) << i for i, (p, q) in enumerate(ps)) | sum((q >> j & 1) << (128 + i) for i, (p, q) in enumerate(ps))
    rows = [row(j) for j in range(N)]
    if len(set(rows)) < N: log('two inputs look alike on the sample'); return None
    t = template()
    a = t.index('def F (x : Fin 6 → Bool)'); head, tail = t[:a], t[a:]
    def rep(old, new, count):
        nonlocal tail
        assert tail.count(old) == count, (old, tail.count(old)); tail = tail.replace(old, new)
    rep('searchN 0 7 ', f'searchN 0 {k} ', 2)
    rep('8 < binaryCost gs', f'{n} < binaryCost gs', 2)
    rep('run_of_build t 8 _', f'run_of_build t {n} _', 1)
    rep("ht' hD 7 (inputs.map", f"ht' hD {k} (inputs.map", 1)
    rep('ws.length ≤ 7 + 2', f'ws.length ≤ {k} + 2', 2)
    rep('root 0 7 3 rowsN = false := root_split 0 7 3 rowsN root_goal pr', f'root 0 {k} {e} rowsN = false := root_split 0 {k} {e} rowsN root_goal pr', 1)
    rep('have e : 7 + 2 - rowsN.length = 3 := by decide', f'have e : {k} + 2 - rowsN.length = {e} := by decide', 1)
    rep('⟨wg, 15⟩', f'⟨wg, {out}⟩', 2)
    rep(f'PEqualNP.Outside.{TEMPLATE_ID}.wg, 15⟩', f'PEqualNP.Outside.{TEMPLATE_ID}.wg, {out}⟩', 2)
    rep('.size = 10 := rfl', f'.size = {m} := rfl', 1)
    rep('  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp', '  rcases hg with ' + ' | '.join(['rfl'] * m) + ' <;> simp', 1)
    # the rows, as bit vectors and as numbers
    w64 = lambda v: [(v >> s) & (2 ** 64 - 1) for s in (192, 128, 64, 0)]
    blk = ''
    for j, v in enumerate(rows): blk += f'def r{j} : W := (' + ' ++ '.join(f'0x{x:x}#64' for x in w64(v)) + ' : BitVec 256)\n'
    blk += 'def rows : List W := [r0, r1, r2, r3, r4, r5]\n'
    for j, v in enumerate(rows):
        x = w64(v); blk += f'def n{j} : ℕ := (((0x{x[0]:x} * 2 ^ 64 + 0x{x[1]:x}) * 2 ^ 64 + 0x{x[2]:x}) * 2 ^ 64 + 0x{x[3]:x})\n'
    i0 = tail.index('def r0 : W := '); i1 = tail.index('def rowsN : List ℕ := ')
    tail = tail[:i0] + blk + tail[i1:]
    # the slices of the root's children: Lean computes the list; past its end a slice is empty and its check trivial
    so = 'set_option maxRecDepth 32000 in\nset_option maxHeartbeats 0 in\n'
    cuts = list(range(0, 40 * slice_len, slice_len)); last = cuts[-1] + slice_len
    ch = f'def kR : List (ℕ × List ℕ) := kidsRoot {e} rowsN\n\n'
    ch += so + f'theorem qr_{last} : anyK (node 0 {k}) (List.drop {last} kR) = false := by\n  decide +kernel\n'
    nxt = last
    for c in reversed(cuts):
        ch += so + f'theorem cr_{c} : anyK (node 0 {k}) (List.take {nxt - c} (List.drop {c} kR)) = false := by\n  decide +kernel\n'
        ch += f'theorem qr_{c} : anyK (node 0 {k}) (List.drop {c} kR) = false :=\n  chainK (node 0 {k}) kR {c} {nxt - c} {nxt} rfl cr_{c} qr_{nxt}\n'
        nxt = c
    ch += f'theorem pr : anyK (node 0 {k}) kR = false := startK _ _ qr_0\n\n'
    i0 = tail.index('def kR : List (ℕ × List ℕ) := kidsRoot 3 rowsN'); i1 = tail.index('theorem root_goal : ')
    tail = tail[:i0] + ch + tail[i1:]
    G = 'PEqualNP.CircuitLowerBounds.GateOp.'
    wg = 'def wg : List PEqualNP.CircuitLowerBounds.Gate := [' + ', '.join(f'⟨{G}{op}, [{x}, {y}]⟩' for op, x, y in gates) + ']'
    lines = tail.split('\n'); hit = 0
    for i, l in enumerate(lines):
        if l.startswith('def wg : List PEqualNP.CircuitLowerBounds.Gate := ['): lines[i] = wg; hit += 1
    assert hit == 1; tail = '\n'.join(lines)
    # the posted statement, verbatim, as the final theorem
    i0 = tail.index(f'theorem PEqualNP.Outside.{TEMPLATE_ID} : '); i1 = tail.index(' := by\n  intro s ⟨C, hfan, hsize, heval⟩', i0)
    tail = tail[:i0] + f'theorem PEqualNP.Outside.{TEMPLATE_ID} : ' + stmt + tail[i1:]
    assert tail.count(T_OLD) >= 3; tail = tail.replace(T_OLD, expr)
    t = (head + tail).replace(TEMPLATE_ID, step.replace('-', '_'))
    note = ('-- The whole proof text is that of the merged ' + TEMPLATE_ID + ' (Ming-Chih Kao, pull request 46159, same repository,\n'
            '-- Apache-2.0); only the data of this function (the 128 sample pairs, the bounds, the slices of the root search and\n'
            '-- the witness circuit) was computed anew.\n')
    t = t.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n' + note, 1)
    return t, dict(m=m, k=k, e=e, near=nnear, seed=seed, slice=slice_len)

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1; sl = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    r = build(step, open(sf).read().strip(), seed, sl)
    if not r: sys.exit(1)
    open(out, 'w').write(r[0]); print('written:', r[1]); sys.exit(0)
