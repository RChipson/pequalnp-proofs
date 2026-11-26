#!/usr/bin/env python3
"""Keep looking for a smaller circuit for a table already in the cache: new annealing runs of the cover
(different seeds and temperatures) and different tie-breaks in the OR sharing.  A better result replaces
best.txt / best.json of the table, where watch_tables.py picks it up.

  python3 generator/keycover/improve.py <table dir> <n> <minutes> [seconds of pair matching per side]"""
import json, os, random, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gencover
d, n, mins = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
PAIR = float(sys.argv[4]) if len(sys.argv) > 4 else 20
BASE = os.path.dirname(d)
end = time.time() + 60 * mins
best = json.load(open(f'{d}/best.json'))['gates']
rnd = random.Random(int(time.time()))
if not os.path.exists(f'{d}/t.txt'):
    rows = json.load(open(f'{d}/table.json'))
    open(f'{d}/t.txt', 'w').write('\n'.join('%016x %016x' % (r >> 64, r & ((1 << 64) - 1)) for r in rows) + '\n')
it = 0
while time.time() < end:
    it += 1
    seed = rnd.randrange(1, 10**9)
    t0 = rnd.choice([0.35, 0.45, 0.55]); t1 = rnd.choice([0.1, 0.12, 0.15])
    subprocess.run([f'{BASE}/sa', str(n), f'{d}/t.txt', f'{d}/best.txt', f'{d}/try.txt', str(seed), '60', str(t0), str(t1)], capture_output=True, check=True)
    blocks = gencover.load_blocks(f'{d}/try.txt')
    for ps in range(2):
        s2 = rnd.randrange(1, 10**9)
        g, o = gencover.build(n, blocks, s2, PAIR)
        if len(g) < best:
            rows = json.load(open(f'{d}/table.json'))
            assert gencover.simulate(n, g, o) == sum(rows[u] << (u * n) for u in range(n))
            best = len(g)
            subprocess.run(['cp', f'{d}/try.txt', f'{d}/best.txt'])
            json.dump({'gates': g, 'out': o}, open(f'{d}/best_circuit.json', 'w'))
            json.dump({'gates': best, 'circuit': 'best_circuit.json'}, open(f'{d}/best.json.new', 'w')); os.replace(f'{d}/best.json.new', f'{d}/best.json')
            print(time.strftime('%H:%M:%S', time.gmtime()), 'better:', best, 'gates', flush=True)
print('done; best', best, 'after', it, 'rounds')
