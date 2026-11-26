#!/usr/bin/env python3
"""Sweep over the open rows "One-a-side promise: the n by m bipartite graph with mask M has a fan-in-two
AND/OR circuit of at most k gates" without a pull request: exact SAT search for the circuit
(generator/encoder/msynth.py); if one exists within the bar, write the witness, compile, lease with
--proof-of and submit.   python3 generator/respond/sweep_rect.py <worker index> <workers> <minutes>"""
import json, os, random, re, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'encoder'))
import auto_respond as A
from msynth import search, check
PAT = re.compile(r'PEqualNP\.Represents\.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) (\d+)')
wi, nw, mins = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
end = time.time() + 60 * mins; done = set()
MEMO = f'{A.D}/rect_memo.json'
while time.time() < end:
    try: G = A.gaps()
    except Exception: time.sleep(20); continue
    try: memo = json.load(open(MEMO))
    except Exception: memo = {}
    rows = []
    for i, g in G.items():
        if not A.is_open(g) or i in done or i in memo or A.num(i) % nw != wi: continue
        m = PAT.fullmatch(' '.join(g.get('statement', '').split()))
        if not m or m.group(2) != m.group(4): continue
        rows.append((i, int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(5))))
    if not rows: A.log(f'[{wi}] nothing left'); time.sleep(60); continue
    rows.sort(key=lambda r: -A.num(r[0]))
    for step, n, mm, mask, bar in rows[:6]:
        done.add(step)
        prom = [((1 << u) | (1 << (n + v)), mask >> (mm * u + v) & 1) for u in range(n) for v in range(mm)]
        R = len(prom); incols = [sum(1 << r for r in range(R) if prom[r][0] >> i & 1) for i in range(n + mm)]
        target = sum(1 << r for r in range(R) if prom[r][1])
        res = None; verdict = 'none'
        for k in range(1, bar + 1):
            res = search(n + mm, incols, R, [target], k, 'andor', 40)
            if isinstance(res, tuple): break
            if res == 'timeout': verdict = 'undecided'; break
        if not isinstance(res, tuple):
            A.log(f'[{wi}]', step, f'{n} by {mm}, bar {bar}:', verdict)
            try: memo = json.load(open(MEMO))
            except Exception: memo = {}
            memo[step] = verdict; json.dump(memo, open(MEMO + f'.{wi}', 'w')); os.replace(MEMO + f'.{wi}', MEMO)
            continue
        gl, outs = res
        g = G[step]; stmt = g['statement'].strip()
        f = f'{A.D}/{step.replace("-", "_")}.lean'
        open(f, 'w').write(A.witness_lean(step, stmt, [(op, [a, b]) for op, a, b in gl], outs[0]))
        if not A.compiles(f): A.log(f'[{wi}]', step, 'does not compile'); continue
        A.log(f'[{wi}]', step, f'{n} by {mm}:', len(gl), 'gates for the bar', bar, '; proof ready')
        A.send(step, f)
A.log(f'[{wi}] time is up')
