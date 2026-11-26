#!/usr/bin/env python3
"""Rows "the two-lit function of the graph H on n points with mask M on shared wires has an AND/OR[/NOT] circuit
of fan-in two with at most k gates": the circuit sees the n points, with one or two of them lit (i and j,
possibly equal), and must output bit n * min(i, j) + max(i, j) of M.  Exact SAT search, smallest size first.

  python3 twolit.py <step id> <statement file> <out.lean> [seconds]
exit 0: witness written; 1: no circuit up to the bar (exhaustive): the row is false; 3: undecided / not this family"""
import os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('mux', 'encoder', 'respond'): sys.path.insert(0, os.path.join(HERE, '..', d))
PAT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.(FanInTwo|Monotone2) C ∧ C\.size ≤ (\d+) ∧ ∀ i j : Fin (\d+), C\.eval \(List\.ofFn fun k : Fin (\d+) => decide \(k = i ∨ k = j\)\) = \((\d+) : ℕ\)\.testBit \((\d+) \* min i\.val j\.val \+ max i\.val j\.val\)')

def parse(stmt):
    m = PAT.fullmatch(' '.join(stmt.split()))
    if not m or not (m.group(3) == m.group(4) == m.group(6)): return None
    return m.group(1) == 'FanInTwo', int(m.group(2)), int(m.group(3)), int(m.group(5))

def rows_of(n, M):
    return [((1 << i) | (1 << j), bool(M >> (n * i + j) & 1)) for i in range(n) for j in range(i, n)]

def one(n, M, k, with_not):
    """gates [(op, [wires])] and the output wire for exactly k gates, or None"""
    rows = rows_of(n, M)
    if with_not:
        import synth_not
        S = synth_not.Synth(n, k, True)
        for x, o in rows: S.add_row(x, o)
        g = S.solve()
        if not g: return None
        return [(t, [a] if t == 'not' else [a, b]) for t, a, b in g], n + k - 1
    from msynth import search
    R = len(rows); incols = [sum(1 << r for r in range(R) if rows[r][0] >> i & 1) for i in range(n)]
    target = sum(1 << r for r in range(R) if rows[r][1])
    res = search(n, incols, R, [target], k, 'andor', 3600)
    if not isinstance(res, tuple): return None
    return [(op, [a, b]) for op, a, b in res[0]], res[1][0]

def check(n, M, gates, out):
    for x, o in rows_of(n, M):
        w = [bool(x >> i & 1) for i in range(n)]
        for op, ins in gates:
            v = [w[a] for a in ins]
            w.append(all(v) if op == 'and' else any(v) if op == 'or' else (not v[0]))
        if w[out] != o: return False
    return True

if __name__ == '__main__':
    if sys.argv[1] == 'one':
        n, M, k, wn = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] == '1'
        print('RES' + repr(one(n, M, k, wn))); sys.exit(0)
    step, sf, out = sys.argv[1:4]; secs = float(sys.argv[4]) if len(sys.argv) > 4 else 90
    stmt = open(sf).read().strip(); p = parse(stmt)
    if not p: print('not a row of this family'); sys.exit(3)
    wn, bar, n, M = p
    t_end = time.time() + secs
    for k in range(1, bar + 1):
        left = t_end - time.time()
        if left < 1: print(f'undecided at {k} gates'); sys.exit(3)
        try: o = subprocess.run([sys.executable, os.path.abspath(__file__), 'one', str(n), str(M), str(k), '1' if wn else '0'], capture_output=True, text=True, timeout=left).stdout.strip()
        except subprocess.TimeoutExpired: print(f'undecided at {k} gates'); sys.exit(3)
        if o.startswith('RES(') or o.startswith('RES['):
            gates, outw = eval(o[3:])
            assert check(n, M, gates, outw) and len(gates) <= bar
            import auto_respond as A
            open(out, 'w').write(A.witness_lean(step, stmt, gates, outw))
            print(f'{len(gates)} gates for the bar {bar}'); sys.exit(0)
    print(f'no circuit of at most {bar} gates (exhaustive search)'); sys.exit(1)
