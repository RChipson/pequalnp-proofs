#!/usr/bin/env python3
"""Short clause-learning (RUP) runs for the pigeonhole formula from real solver runs.

Each trial: rename the variables and shuffle the clauses at random, let a CDCL solver (through
PySAT, proof logging on) refute the formula, take the clauses it learned in order, map them back,
add the empty clause, check the run with the independent checker of rupsearch.py, keep only the
clauses the final conflict depends on, then drop further clauses one at a time while the run stays
valid.  The shortest run over all trials is kept.

  python3 cdclruns.py <pigeons> <holes> <target> <seconds> [seed] [solver names, comma separated]"""
import random, sys, time
from pysat.solvers import Solver
from rupsearch import php, up, check_run, shorten

def up_used(db, nv, assume):
    """Unit propagation that also returns the indices of the clauses used to reach the conflict."""
    val = {}; reason = {}
    for l in assume: val[abs(l)] = l > 0
    changed = True
    while changed:
        changed = False
        for ci, c in enumerate(db):
            un = None; n_un = 0; sat = False
            for l in c:
                v = val.get(abs(l))
                if v is None: n_un += 1; un = l
                elif v == (l > 0): sat = True; break
            if sat: continue
            if n_un == 0:
                used = set(); stack = [ci]
                while stack:
                    k = stack.pop()
                    if k in used: continue
                    used.add(k)
                    for l in db[k]:
                        r = reason.get(abs(l))
                        if r is not None and r != k: stack.append(r)
                return True, used
            if n_un == 1:
                val[abs(un)] = un > 0; reason[abs(un)] = ci; changed = True
    return False, set()

def trim(F, nv, run):
    """Keep only the learned clauses the (first) empty clause depends on."""
    k = next(i for i, c in enumerate(run) if len(c) == 0); run = run[:k + 1]
    db = [list(c) for c in F] + [list(c) for c in run]; nf = len(F)
    need = {nf + k}
    for i in range(k, -1, -1):
        if nf + i not in need: continue
        ok, used = up_used(db[:nf + i], nv, [-l for l in run[i]])
        assert ok
        need |= {u for u in used if u >= nf}
    return [run[i] for i in range(k + 1) if nf + i in need]

def trial(F, nv, rnd, name):
    perm = list(range(1, nv + 1)); rnd.shuffle(perm)
    sign = [rnd.choice((1, -1)) for _ in range(nv + 1)]
    fwd = lambda l: (perm[abs(l) - 1] * sign[abs(l)]) * (1 if l > 0 else -1)
    inv = {}
    for v in range(1, nv + 1): inv[perm[v - 1]] = v * sign[v]
    back = lambda l: inv[abs(l)] * (1 if l > 0 else -1)
    G = [[fwd(l) for l in c] for c in F]
    for c in G: rnd.shuffle(c)
    rnd.shuffle(G)
    with Solver(name=name, bootstrap_with=G, with_proof=True) as s:
        assert s.solve() is False
        proof = s.get_proof()
    run = []
    for line in proof:
        t = line.split()
        if not t or t[0] == 'd': continue
        run.append([back(int(x)) for x in t[:-1]])
    if not any(len(c) == 0 for c in run): run.append([])
    return run

def main():
    m, n, target, secs = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    names = sys.argv[6].split(',') if len(sys.argv) > 6 else ['g4', 'm22', 'g3', 'mgh', 'lgl']
    rnd = random.Random(seed); F, nv = php(m, n)
    best = None; t0 = time.time(); k = 0; hist = {}
    while time.time() - t0 < secs:
        k += 1; name = names[k % len(names)]
        try: run = trial(F, nv, rnd, name)
        except Exception as e:
            if k < 12: print('solver', name, 'failed:', repr(e)[:80], flush=True)
            continue
        if not check_run(F, nv, run): continue
        raw = len(run); run = trim(F, nv, run); t1 = len(run)
        if best is None or len(run) <= len(best) + 6: run = shorten(F, nv, run, rnd)
        assert check_run(F, nv, run)
        hist[len(run)] = hist.get(len(run), 0) + 1
        if best is None or len(run) < len(best):
            best = run; print('length', len(run), '(raw', raw, 'trimmed', t1, ') solver', name, 'trial', k, '%.0f s' % (time.time() - t0), flush=True)
            if len(run) <= target: break
    print('trials', k, 'histogram', sorted(hist.items())[:8])
    print('BEST', len(best)); print(best)

if __name__ == '__main__':
    main()
