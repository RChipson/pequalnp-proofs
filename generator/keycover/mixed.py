#!/usr/bin/env python3
"""AND/OR circuits for a small graph on the one-a-side promise, with mixed ORs.

A cover of the ones by all-ones blocks (S x T) gives the circuit OR over blocks of (OR S) AND (OR T).  Two
blocks (S, T) and (S', T') can instead share one AND gate:  (OR S or OR T') AND (OR S' or OR T)  is, on the
promise, the union of S x T, S' x T', the full rows of S and S' common to both and the full columns common to
T and T'; it is used when all of those cells are ones.  The count of gates before sharing is the same, but
the ORs now run over rows and columns together, which shares better (cse.paar on sets over all 2n wires).

best(n, mask, tries, seconds) -> (gates, out) or None"""
import itertools, os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gencover
from cse import paar
S_ = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
BASE = f'{S_}/desk/big/tables'

def covers(n, mask, tries):
    import small
    small.tools()
    rows = [(mask >> (n * u)) & ((1 << n) - 1) for u in range(n)]
    d = tempfile.mkdtemp(prefix='mixed_', dir=f'{S_}/desk/big')
    h = lambda x: '%016x %016x' % (x >> 64, x & ((1 << 64) - 1))
    open(f'{d}/t.txt', 'w').write('\n'.join(h(r) for r in rows) + '\n')
    with open(f'{d}/c0.txt', 'w') as f:
        for u in range(n):
            if rows[u]: f.write('B %s %s\n' % (h(1 << u), h(rows[u])))
    out = []
    for t in range(tries):
        t0, t1 = [('0.9', '0.12'), ('0.7', '0.2'), ('1.2', '0.3'), ('0.9', '0.4')][t % 4]
        subprocess.run([f'{BASE}/sa', str(n), f'{d}/t.txt', f'{d}/c0.txt', f'{d}/s.txt', str(t + 1), '3', t0, t1], capture_output=True, check=True)
        out.append(gencover.load_blocks(f'{d}/s.txt'))
    subprocess.run(['rm', '-rf', d])
    return out

def cost_and_build(n, terms, rnd, build=False):
    """terms: list of (set, set) of wires (0..n-1 rows, n..2n-1 columns): the term is (OR set1) AND (OR set2)"""
    sets = []
    for a, b in terms: sets += [frozenset(a), frozenset(b)]
    g, defs, cur = paar(sets, rnd)
    total = g + len(terms) + len(terms) - 1
    if not build: return total
    gates = []; wire = {i: i for i in range(2 * n)}
    for z, a, b in defs:
        gates.append(('or', wire[a], wire[b])); wire[z] = 2 * n + len(gates) - 1
    outw = []; memo = {}
    for s in cur:
        k = frozenset(s)
        if k not in memo:
            l = sorted(wire[i] for i in s); w = l[0]
            for x in l[1:]:
                gates.append(('or', min(w, x), max(w, x))); w = 2 * n + len(gates) - 1
            memo[k] = w
        outw.append(memo[k])
    acc = None
    for t in range(len(terms)):
        x, y = outw[2 * t], outw[2 * t + 1]
        gates.append(('and', min(x, y), max(x, y))); w = 2 * n + len(gates) - 1
        if acc is None: acc = w
        else: gates.append(('or', acc, w)); acc = 2 * n + len(gates) - 1
    return gates, acc

def best(n, mask, tries=6, seconds=8.0, seed=1, given=None):
    rnd = random.Random(seed)
    ones = lambda u, v: mask >> (n * u + v) & 1
    full_row = [all(ones(u, v) for v in range(n)) for u in range(n)]
    full_col = [all(ones(u, v) for u in range(n)) for v in range(n)]
    target = sum(1 << (u * n + v) for u in range(n) for v in range(n) if ones(u, v))
    bestc = None
    for blocks in (given if given is not None else covers(n, mask, tries)):
        B = [([u for u in range(n) if S >> u & 1], [v for v in range(n) if T >> v & 1]) for S, T in blocks]
        m = len(B)
        def ok(j, k):
            Sj, Tj = B[j]; Sk, Tk = B[k]
            return all(full_row[u] for u in set(Sj) & set(Sk)) and all(full_col[v] for v in set(Tj) & set(Tk))
        def terms_of(match):
            used = set(); T = []
            for j, k in match:
                used |= {j, k}
                T.append((set(B[j][0]) | {n + v for v in B[k][1]}, set(B[k][0]) | {n + v for v in B[j][1]}))
            for j in range(m):
                if j not in used: T.append((set(B[j][0]), {n + v for v in B[j][1]}))
            return T
        pairs = [(j, k) for j in range(m) for k in range(j + 1, m) if ok(j, k)]
        per = time.time() + seconds / max(1, tries)
        first = True
        while first or time.time() < per:
            first = False
            # a random start, then hill climbing over matchings
            cur = []; rnd.shuffle(pairs)
            for j, k in pairs:
                used = {x for p in cur for x in p}
                if j not in used and k not in used and rnd.random() < 0.5: cur.append((j, k))
            curc = min(cost_and_build(n, terms_of(cur), rnd) for _ in range(2))
            while time.time() < per:
                improved = False
                rnd.shuffle(pairs)
                for j, k in pairs:
                    used = {x for p in cur for x in p}
                    if (j, k) in cur: cand = [p for p in cur if p != (j, k)]
                    elif j not in used and k not in used: cand = cur + [(j, k)]
                    else: cand = [p for p in cur if not ({j, k} & set(p))] + [(j, k)]
                    c = min(cost_and_build(n, terms_of(cand), rnd) for _ in range(2))
                    if c < curc: improved = True; cur, curc = cand, c
                if not improved: break
            for _ in range(4):
                g, o = cost_and_build(n, terms_of(cur), rnd, True)
                if gencover.simulate(n, g, o) == target and (bestc is None or len(g) < len(bestc[0])): bestc = (g, o)
    return bestc

if __name__ == '__main__':
    n, mask = int(sys.argv[1]), int(sys.argv[2]); tries = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    t = time.time(); c = best(n, mask, tries)
    print(len(c[0]) if c else None, 'gates', round(time.time() - t, 1), 's')
