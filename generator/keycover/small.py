#!/usr/bin/env python3
"""Small graphs (side up to 16) given by a mask: an AND/OR circuit for the one-a-side promise from a cover of
the ones by all-ones blocks with shared ORs, as in gencover.py.  The cover is annealed from several starts.

best(n, mask, tries) -> (gates [(op, a, b)], output wire);  python3 small.py <n> <mask> [tries]"""
import json, os, random, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gencover
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
BASE = f'{S}/desk/big/tables'
def tools():
    os.makedirs(BASE, exist_ok=True)
    for t in ('pick3', 'sa'):
        if not os.path.exists(f'{BASE}/{t}'): subprocess.run(['gcc', '-O2', '-o', f'{BASE}/{t}', f'{HERE}/{t}.c', '-lm'], check=True)
def best(n, mask, tries=6, pair_seconds=0.6):
    tools()
    rows = [(mask >> (n * u)) & ((1 << n) - 1) for u in range(n)]
    d = tempfile.mkdtemp(prefix='small_', dir=f'{S}/desk/big')
    h = lambda x: '%016x %016x' % (x >> 64, x & ((1 << 64) - 1))
    open(f'{d}/t.txt', 'w').write('\n'.join(h(r) for r in rows) + '\n')
    cols = [sum(((rows[u] >> v) & 1) << u for u in range(n)) for v in range(n)]
    # start: one block per row and one per column (the annealer reshapes them)
    with open(f'{d}/c0.txt', 'w') as f:
        for u in range(n):
            if rows[u]: f.write('B %s %s\n' % (h(1 << u), h(rows[u])))
    target = sum(rows[u] << (u * n) for u in range(n))
    bestc = None
    for t in range(tries):
        subprocess.run([f'{BASE}/sa', str(n), f'{d}/t.txt', f'{d}/c0.txt', f'{d}/s.txt', str(t + 1), '3', '0.9', '0.12'], capture_output=True, check=True)
        blocks = gencover.load_blocks(f'{d}/s.txt')
        for seed in (t + 1, t + 101):
            for ps in (0, pair_seconds):
                g, o = gencover.build(n, blocks, seed, ps)
                if gencover.simulate(n, g, o) == target and (bestc is None or len(g) < len(bestc[0])): bestc = (g, o)
    subprocess.run(['rm', '-rf', d])
    return bestc
if __name__ == '__main__':
    n, mask = int(sys.argv[1]), int(sys.argv[2]); tries = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    g, o = best(n, mask, tries); print(len(g), 'gates', g, o)
