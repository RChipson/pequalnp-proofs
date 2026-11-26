#!/usr/bin/env python3
"""Fast survey of the promise-representation family: for each (side, mask) try the bars from the
largest down, each exact search limited to a few seconds, three groups at a time.  Writes one JSON
file per provable row: <out dir>/<step id>.json = {n, mask, bar, gates}.

  python3 survey.py <gaps.json> <out dir> [seconds per search]"""
import json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import genprom

def one(n, mask, k, secs):
    try:
        r = subprocess.run([sys.executable, '-c', f'import sys; sys.path.insert(0, {HERE!r}); import genprom; print(repr(genprom.circuit({n}, {mask}, {k})))'], capture_output=True, text=True, timeout=secs)
    except subprocess.TimeoutExpired:
        return 'timeout'
    return eval(r.stdout.strip()) if r.stdout.strip() else 'timeout'

def group(key, rows, outdir, secs):
    n, mask = key; bars = sorted({b for _, b in rows}, reverse=True); best = None; log = []
    todo = list(bars)
    while todo:
        b = todo[0]
        if best is not None and len(best) <= b:
            todo.pop(0); continue
        g = one(n, mask, b, secs)
        if g is None and b > 1:          # exactly b gates all used is impossible: one fewer may still work
            g = one(n, mask, b - 1, secs)
        log.append((b, 'yes' if isinstance(g, list) else str(g)))
        if not isinstance(g, list): break
        best = g
        # try to shrink further below this bar straight away
    if best is not None:
        for x, o in genprom.rows_of(n, mask): assert genprom.synth_not.evalc(2 * n, best, x) == o
        for sid, b in rows:
            if len(best) <= b: json.dump(dict(n=n, mask=mask, bar=b, gates=best), open(f'{outdir}/{sid}.json', 'w'))
    print(n, mask, 'bars', bars, '->', log, 'size', len(best) if best else None, flush=True)

def main():
    gaps = json.load(open(sys.argv[1]))['gaps']; outdir = sys.argv[2]; secs = float(sys.argv[3]) if len(sys.argv) > 3 else 15
    os.makedirs(outdir, exist_ok=True); groups = {}
    for g in gaps:
        p = genprom.parse(g.get('statement', ''))
        if p and str(g.get('pr_open', '0')) in ('0', 'None'): groups.setdefault((p[0], p[1]), []).append((g['id'], p[2]))
    minbar = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    groups = {k: v for k, v in groups.items() if max(b for _, b in v) >= minbar}
    print('groups', len(groups), 'rows', sum(len(v) for v in groups.values()), flush=True)
    with ThreadPoolExecutor(3) as ex:
        list(ex.map(lambda kv: group(kv[0], kv[1], outdir, secs), sorted(groups.items(), key=lambda kv: -max(b for _, b in kv[1]))))

if __name__ == '__main__':
    main()
