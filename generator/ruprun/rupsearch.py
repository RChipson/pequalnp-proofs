#!/usr/bin/env python3
"""Short clause-learning runs (RUP runs) for the pigeonhole formula with m pigeons and n holes.

A run is a list of clauses, each of which is RUP over the formula and the clauses before it
(assuming all its literals false, unit propagation falsifies a clause); it must contain the
empty clause.  This program builds runs by a randomised decision search: refute(D) for a list D
of decision literals propagates; on a conflict it learns the negation of a minimal conflicting
subset of D; otherwise it picks a literal x, refutes D + [x], and goes on.  Every learned clause
is RUP when it is learned.  The run is then re-checked by an independent checker and shortened
by dropping clauses that are not needed.

  python3 rupsearch.py <pigeons> <holes> <target length> <seconds> [seed]
Prints the best run found (clauses as lists of (pigeon, hole, sign), oldest first)."""
import random, sys, time

def php(m, n):
    var = lambda i, j: i * n + j + 1
    F = [[var(i, j) for j in range(n)] for i in range(m)]
    for j in range(n):
        for a in range(m):
            for b in range(a + 1, m): F.append([-var(a, j), -var(b, j)])
    return F, m * n

def up(clauses, nv, assume):
    """Unit propagation.  Returns (conflict?, assignment dict)."""
    val = {}
    for l in assume:
        if val.get(abs(l)) == (l < 0): return True, val      # contradictory assumptions
        val[abs(l)] = l > 0
    changed = True
    while changed:
        changed = False
        for c in clauses:
            unassigned = None; n_un = 0; sat = False
            for l in c:
                v = val.get(abs(l))
                if v is None:
                    n_un += 1; unassigned = l
                elif v == (l > 0): sat = True; break
            if sat: continue
            if n_un == 0: return True, val
            if n_un == 1:
                val[abs(unassigned)] = unassigned > 0; changed = True
    return False, val

def check_run(F, nv, run):
    """Independent check: every clause RUP over F and the earlier ones; the empty clause present."""
    db = [list(c) for c in F]
    for c in run:
        conf, _ = up(db, nv, [-l for l in c])
        if not conf: return False
        db.append(list(c))
    return any(len(c) == 0 for c in run)

def shorten(F, nv, run, rnd):
    """Drop clauses while the run stays valid (tries in random order, repeated)."""
    run = [list(c) for c in run]
    k = len(run) - 1 - next(i for i, c in enumerate(reversed(run)) if len(c) == 0)
    run = run[:k + 1]                       # nothing after the first empty clause... keep up to the last one
    improved = True
    while improved:
        improved = False
        idx = list(range(len(run) - 1)); rnd.shuffle(idx)
        for i in idx:
            if i >= len(run) - 1: continue
            cand = run[:i] + run[i + 1:]
            if check_run(F, nv, cand): run = cand; improved = True
    return run

def one_run(F, nv, rnd, limit, mode):
    db = [list(c) for c in F]; run = []
    class Over(Exception): pass
    def minimise(D):
        S = list(D); order = list(S); rnd.shuffle(order)
        if mode & 1: order = list(reversed(D))
        for l in order:
            T = [x for x in S if x != l]
            if up(db, nv, T)[0]: S = T
        return S
    def refute(D):
        while True:
            conf, val = up(db, nv, D)
            if conf:
                S = minimise(D)
                c = [-l for l in S]; run.append(c); db.append(c)
                if len(run) > limit: raise Over()
                return set(S)
            free = [v for v in range(1, nv + 1) if v not in val]
            v = rnd.choice(free)
            if mode & 2:
                # prefer a variable in a shortest not yet satisfied clause
                best = None
                for cl in db:
                    if any(val.get(abs(l)) == (l > 0) for l in cl): continue
                    un = [l for l in cl if abs(l) not in val]
                    if un and (best is None or len(un) < len(best) or (len(un) == len(best) and rnd.random() < 0.3)): best = un
                v = abs(rnd.choice(best))
            x = v if (rnd.random() < (0.85 if mode & 4 else 0.5)) else -v
            S = refute(D + [x])
            if x not in S: return S
    try:
        refute([])
    except Over:
        return None
    return run

def main():
    m, n, target, secs = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    rnd = random.Random(seed); F, nv = php(m, n)
    best = None; t0 = time.time(); runs = 0
    while time.time() - t0 < secs:
        runs += 1
        lim = (len(best) + 6) if best else 400
        r = one_run(F, nv, rnd, lim, rnd.randrange(8))
        if r is None: continue
        assert check_run(F, nv, r)
        r = shorten(F, nv, r, rnd)
        assert check_run(F, nv, r)
        if best is None or len(r) < len(best):
            best = r; print('length', len(r), 'after', runs, 'runs, %.0f s' % (time.time() - t0), flush=True)
            if len(r) <= target: break
    dec = lambda l: ((abs(l) - 1) // n, (abs(l) - 1) % n, l > 0)
    print('BEST', len(best)); print([[dec(l) for l in c] for c in best])

if __name__ == '__main__':
    main()
