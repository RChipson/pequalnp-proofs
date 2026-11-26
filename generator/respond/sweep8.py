#!/usr/bin/env python3
"""Sweep over the open rows "the n by n graph with mask M is represented on the one-a-side promise by an AND/OR
circuit of fan-in two with at most k gates" (RepSizeAtMost, mask form) that have no pull request: build a
circuit with the mixed-OR block tool (generator/keycover/mixed.py); where it meets the bar, write the witness
proof, compile it, ask the desk for the step with --proof-of and submit.
  python3 generator/respond/sweep8.py <worker index> <workers> <minutes> [tries] [seconds per row] [near]"""
import json, os, random, re, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'keycover'))
import auto_respond as A, small, mixed
PAT = re.compile(r'PEqualNP\.Represents\.RepSizeAtMost \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) (\d+)')
wi, nw, mins = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]); tries = int(sys.argv[4]) if len(sys.argv) > 4 else 6
end = time.time() + 60 * mins
MEMO = f'{A.D}/sweep8m_memo.json'
SECS = float(sys.argv[5]) if len(sys.argv) > 5 else 5.0
NEAR = int(sys.argv[6]) if len(sys.argv) > 6 else 99      # second passes: only rows whose best so far is within NEAR of the bar
def memo_load():
    try: return json.load(open(MEMO))
    except Exception: return {}
done = set()
while time.time() < end:
    try: G = A.gaps()
    except Exception: time.sleep(20); continue
    memo = memo_load()
    rows = []
    for i, g in G.items():
        if not A.is_open(g) or i in done or A.num(i) % nw != wi: continue
        m = PAT.fullmatch(' '.join(g.get('statement', '').split()))
        if not m or m.group(1) != m.group(3) or int(m.group(1)) > 16: continue
        if i in memo and memo[i] > int(m.group(4)) and (NEAR == 99 or memo[i] - int(m.group(4)) > NEAR): continue      # tried before: above the bar
        if NEAR != 99 and i not in memo: continue
        rows.append((i, int(m.group(1)), int(m.group(2)), int(m.group(4))))
    if not rows: A.log(f'[{wi}] nothing left'); time.sleep(120); continue
    random.shuffle(rows)
    for step, n, mask, bar in rows[:8]:
        done.add(step)
        t = time.time(); c = mixed.best(n, mask, tries, SECS, random.randrange(1 << 20))
        if c is None: continue
        gl, out = c
        memo = memo_load(); memo[step] = min(len(gl), memo.get(step, 999)); json.dump(memo, open(MEMO + f'.{wi}', 'w')); os.replace(MEMO + f'.{wi}', MEMO)
        if len(gl) > bar: A.log(f'[{wi}]', step, len(gl), 'gates, bar', bar); continue
        g = G[step]; stmt = g['statement'].strip()
        f = f'{A.D}/{step.replace("-", "_")}.lean'
        open(f, 'w').write(A.witness_lean(step, stmt, [(op, [a, b]) for op, a, b in gl], out))
        if not A.compiles(f): A.log(f'[{wi}]', step, 'does not compile'); continue
        A.log(f'[{wi}]', step, len(gl), 'gates for the bar', bar, '; proof ready after', round(time.time() - t), 's')
        A.send(step, f)
A.log(f'[{wi}] time is up')
