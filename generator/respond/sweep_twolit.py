#!/usr/bin/env python3
"""Sweep over the open two-lit rows without a pull request: exact search (generator/twolit/twolit.py); a row
with a circuit within its bar is sent (lease with --proof-of).  Rows shown false are remembered.
  python3 generator/respond/sweep_twolit.py <worker index> <workers> <minutes>"""
import json, os, random, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import auto_respond as A
wi, nw, mins = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
end = time.time() + 60 * mins; MEMO = f'{A.D}/twolit_memo_{wi}.json'
memo = json.load(open(MEMO)) if os.path.exists(MEMO) else {}
found = 0
while time.time() < end:
    try: G = A.gaps()
    except Exception: time.sleep(20); continue
    rows = [i for i, g in G.items() if g.get('title', '').startswith('The two-lit function') and A.is_open(g) and i not in memo and A.num(i) % nw == wi]
    if not rows: A.log(f'[{wi}] nothing left; sent', found); time.sleep(300); continue
    random.shuffle(rows)
    for step in rows[:25]:
        g = G[step]; stmt = g['statement'].strip()
        sf = f'{A.D}/stmt_{step}.txt'; open(sf, 'w').write(stmt); out = f'{A.D}/{step.replace("-", "_")}.lean'
        try: r = subprocess.run(['python3', os.path.join(A.GEN, 'twolit', 'twolit.py'), step, sf, out, '45'], capture_output=True, text=True, timeout=70); rc = r.returncode
        except subprocess.TimeoutExpired: rc = 3
        memo[step] = rc; json.dump(memo, open(MEMO, 'w'))
        if rc != 0: continue
        if not A.compiles(out): A.log(f'[{wi}]', step, 'does not compile'); continue
        A.log(f'[{wi}]', step, r.stdout.strip()[-40:], '; proof ready')
        if A.send(step, out): found += 1
A.log(f'[{wi}] time is up; sent', found)
