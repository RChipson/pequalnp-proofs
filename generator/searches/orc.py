# Fewest OR gates (AND gates free) in a monotone circuit that is true on given
# minimal true rows and false on given maximal false rows.
import sys, itertools
from pysat.solvers import Cadical153

def solve(n, trues, falses, t, verbose=False):
    # trues/falses: lists of sets of input indices that are 1
    vid = [0]
    def new():
        vid[0] += 1; return vid[0]
    cls = []
    sel = [[[new() for j in range(n+i)] for a in (0,1)] for i in range(t)]
    outsel = [new() for j in range(n+t)]
    def rowvars(r):
        return [new() for i in range(t)]
    for r in trues:
        v = [None]*n + rowvars(r)
        def val(j): return (j in r) if j < n else v[j]
        for j in range(n+t):
            x = val(j)
            if x is True: continue
            if x is False: cls.append([-outsel[j]])
            else: cls.append([-outsel[j], x])
        for i in range(t):
            tt = [new(), new()]
            cls.append([-v[n+i], tt[0], tt[1]])
            for a in (0,1):
                for j in range(n+i):
                    x = val(j)
                    if x is True: continue
                    if x is False: cls.append([-tt[a], -sel[i][a][j]])
                    else: cls.append([-tt[a], -sel[i][a][j], x])
    for r in falses:
        v = [None]*n + rowvars(r)
        def val(j): return (j in r) if j < n else v[j]
        def falsified(selrow, upto):
            lits = []
            for j in range(upto):
                x = val(j)
                if x is True: continue
                if x is False: lits.append(selrow[j])
                else:
                    u = new(); cls.append([-u, selrow[j]]); cls.append([-u, -x]); lits.append(u)
            return lits
        cls.append(falsified(outsel, n+t))
        for i in range(t):
            for a in (0,1):
                tt = new()
                cls.append([-tt, v[n+i]])
                cls.append([tt] + falsified(sel[i][a], n+i))
    s = Cadical153(bootstrap_with=cls)
    ok = s.solve()
    res = None
    if ok:
        m = set(x for x in s.get_model() if x > 0)
        res = ([[ [j for j in range(n+i) if sel[i][a][j] in m] for a in (0,1)] for i in range(t)],
               [j for j in range(n+t) if outsel[j] in m])
    s.delete()
    return ok, res

def mis(n, edges):
    adj = [set() for _ in range(n)]
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    out = []
    def rec(cur, cand, excl):
        if not cand and not excl: out.append(frozenset(cur)); return
        for v in list(cand):
            rec(cur|{v}, cand - adj[v] - {v}, excl - adj[v] - {v})
            cand = cand - {v}; excl = excl | {v}
    rec(set(), set(range(n)), set())
    return out

def evalc(n, circ, x):
    gates, outs = circ
    v = [(j in x) for j in range(n)]
    for g in gates:
        v.append(all(v[j] for j in g[0]) or all(v[j] for j in g[1]))
    return all(v[j] for j in outs)

if __name__ == '__main__':
    tests = {
      'path3': (4, [(0,1),(1,2),(2,3)]),
      'C6': (6, [(i,(i+1)%6) for i in range(6)]),
      'C8': (8, [(i,(i+1)%8) for i in range(8)]),
      'C5': (5, [(i,(i+1)%5) for i in range(5)]),
    }
    for name,(n,E) in tests.items():
        M = mis(n,E)
        for t in range(0, len(E)):
            ok,res = solve(n, [set(e) for e in E], [set(m) for m in M], t)
            if ok:
                # verify on all inputs
                good = all(evalc(n,res,set(j for j in range(n) if x>>j&1)) == any((x>>a&1) and (x>>b&1) for a,b in E) for x in range(1<<n))
                print(name, 'edges', len(E), 'min ORs', t, 'verified', good, res, flush=True)
                break
