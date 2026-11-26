#!/usr/bin/env python3
"""Shrink a monotone (AND/OR, fan-in two) circuit that is right on given rows, one gate at a time, by local
rewriting with a SAT solver: a run of k consecutive gates is replaced by k - 1 free gates; later gates keep
their operation, and those of their inputs that read a removed gate may be pointed anywhere earlier.

shrink(nin, incols, R, target, gates, out, goal, seconds) -> (gates, out)   (gates: (op, a, b), wires 0..nin-1 inputs)"""
import os, random, subprocess, sys, tempfile, time

def evalc(nin, incols, gates):
    W = list(incols)
    for o, a, b in gates: W.append(W[a] & W[b] if o == 'and' else W[a] | W[b])
    return W

def prune(nin, gates, out):
    """drop gates the output does not depend on; renumber"""
    need = set(); st = [out]
    while st:
        w = st.pop()
        if w < nin or w in need: continue
        need.add(w); o, a, b = gates[w - nin]; st += [a, b]
    keep = sorted(need); idx = {w: nin + i for i, w in enumerate(keep)}
    f = lambda w: w if w < nin else idx[w]
    return [(gates[w - nin][0], f(gates[w - nin][1]), f(gates[w - nin][2])) for w in keep], f(out)

def shuffle_topo(nin, gates, out, rnd):
    """a random topological order of the gates"""
    G = len(gates); deps = [set(x - nin for x in (a, b) if x >= nin) for o, a, b in gates]
    placed = []; done = set(); left = set(range(G))
    while left:
        ready = [g for g in left if deps[g] <= done]
        # prefer to keep related gates close: pick among the ready ones at random
        g = rnd.choice(ready); placed.append(g); done.add(g); left.discard(g)
    idx = {nin + g: nin + i for i, g in enumerate(placed)}
    f = lambda w: w if w < nin else idx[w]
    return [(gates[g][0], f(gates[g][1]), f(gates[g][2])) for g in placed], f(out)

def try_window(nin, incols, R, target, gates, out, i, k, seconds, seed=0):
    G = len(gates); W = evalc(nin, incols, gates)
    P = nin + i                               # wires 0..P-1 are fixed (inputs and the gates before the window)
    nf = k - 1
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cl = []
    def link(sel, T, x):                      # sel -> (T <-> x), x a literal or a constant
        if x is True: cl.append([-sel, T])
        elif x is False: cl.append([-sel, -T])
        else: cl.append([-sel, -T, x]); cl.append([-sel, T, -x])
    fv = [[new() for r in range(R)] for j in range(nf)]; fop = [new() for j in range(nf)]
    fsa = []; fsb = []
    def cand(limit):                          # wires a free selector may read: fixed wires and free gates below `limit`
        return list(range(P)) + [('f', j) for j in range(limit)]
    def val(w, r):
        if isinstance(w, tuple): return fv[w[1]][r]
        return bool(W[w] >> r & 1)
    def selector(cands):
        s = [new() for _ in cands]; cl.append(s[:])
        for x in range(len(s)):
            for y in range(x + 1, len(s)): cl.append([-s[x], -s[y]])
        return s
    for j in range(nf):
        C = cand(j); a = selector(C); b = selector(C); fsa.append(a); fsb.append(b)
        for x in range(len(C)):
            for y in range(0, x + 1): cl.append([-a[x], -b[y]])          # first operand below the second
        for r in range(R):
            A = new(); B = new()
            for x, w in enumerate(C): link(a[x], A, val(w, r)); link(b[x], B, val(w, r))
            y, o = fv[j][r], fop[j]
            cl += [[o, -y, A, B], [o, y, -A], [o, y, -B], [-o, y, -A, -B], [-o, -y, A], [-o, -y, B]]
    # the gates after the window
    sv = {}                                   # old wire -> per-row literal/constant list
    removed = set(range(P, P + k))
    C_all = cand(nf)
    repoint = {}
    def wire_vals(w):
        if w < P: return [bool(W[w] >> r & 1) for r in range(R)]
        return sv[w]
    for g in range(i + k, G):
        o, a, b = gates[g]; ins = []
        dep = False
        for w in (a, b):
            if w in removed:
                s = selector(C_all); T = [new() for r in range(R)]
                for r in range(R):
                    for x, c in enumerate(C_all): link(s[x], T[r], val(c, r))
                repoint[(g, w, len(ins))] = s; ins.append(T); dep = True
            else:
                v = wire_vals(w); ins.append(v)
                if any(not isinstance(x, bool) for x in v): dep = True
        if not dep: sv[nin + g] = [bool(W[nin + g] >> r & 1) for r in range(R)]; continue
        Y = [new() for r in range(R)]
        for r in range(R):
            A, B, y = ins[0][r], ins[1][r], Y[r]
            def lit(x, neg):
                if isinstance(x, bool): return None if x != neg else 'T'       # None: literal false; 'T': literal true
                return -x if neg else x
            def add(cs):
                out_ = []
                for x in cs:
                    if x == 'T': return
                    if x is not None: out_.append(x)
                cl.append(out_)
            if o == 'or':
                add([-y, lit(A, False), lit(B, False)]); add([y, lit(A, True)]); add([y, lit(B, True)])
            else:
                add([y, lit(A, True), lit(B, True)]); add([-y, lit(A, False)]); add([-y, lit(B, False)])
        sv[nin + g] = Y
    # the output
    if out in removed:
        s = selector(C_all); repoint[('out',)] = s
        for r in range(R):
            t = bool(target >> r & 1)
            for x, c in enumerate(C_all):
                v = val(c, r)
                if isinstance(v, bool):
                    if v != t: cl.append([-s[x]])
                else: cl.append([-s[x], v if t else -v])
    elif out < P: return None
    else:
        for r in range(R):
            v = sv[out][r]; t = bool(target >> r & 1)
            if isinstance(v, bool):
                if v != t: return None
            else: cl.append([v if t else -v])
    fd, path = tempfile.mkstemp(suffix='.cnf'); os.close(fd)
    with open(path, 'w') as f:
        f.write('p cnf %d %d\n' % (nv[0], len(cl)))
        for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
    try: r = subprocess.run(['cadical', '-q', '-t', str(max(1, int(seconds))), '--seed=%d' % seed, path], capture_output=True, text=True)
    finally: os.unlink(path)
    if r.returncode != 10: return None
    model = set()
    for line in r.stdout.split('\n'):
        if line.startswith('v'): model.update(int(x) for x in line.split()[1:] if int(x) > 0)
    def pick(s, C):
        c = C[[x for x in range(len(s)) if s[x] in model][0]]
        return ('f', c[1]) if isinstance(c, tuple) else c
    # rebuild: fixed gates, free gates, later gates
    newg = list(gates[:i]); fw = {}
    for j in range(nf):
        C = cand(j); a = pick(fsa[j], C); b = pick(fsb[j], C)
        m = lambda w: fw[w[1]] if isinstance(w, tuple) else w
        newg.append(('and' if fop[j] in model else 'or', m(a), m(b))); fw[j] = nin + len(newg) - 1
    m = lambda w: fw[w[1]] if isinstance(w, tuple) else w
    old2new = {w: w for w in range(P)}
    for g in range(i + k, G):
        o, a, b = gates[g]; ins = []
        for pos, w in enumerate((a, b)):
            if w in removed: ins.append(m(pick(repoint[(g, w, pos)], C_all)))
            else: ins.append(old2new[w])
        newg.append((o, ins[0], ins[1])); old2new[nin + g] = nin + len(newg) - 1
    nout = m(pick(repoint[('out',)], C_all)) if out in removed else old2new[out]
    if evalc(nin, incols, newg)[nout] != target: return None
    return prune(nin, newg, nout)

def shrink(nin, incols, R, target, gates, out, goal, seconds, seed=1, k=6, per=4):
    rnd = random.Random(seed); t_end = time.time() + seconds
    gates, out = prune(nin, gates, out)
    assert evalc(nin, incols, gates)[out] == target
    fails = 0
    while len(gates) > goal and time.time() < t_end:
        gates, out = shuffle_topo(nin, gates, out, rnd)
        G = len(gates); kk = min(k + (fails // 12), 9, G)
        i = rnd.randrange(0, G - kk + 1)
        res = try_window(nin, incols, R, target, gates, out, i, kk, per, rnd.randrange(1 << 20))
        if res and len(res[0]) < len(gates): gates, out = res; fails = 0
        else: fails += 1
    return gates, out

if __name__ == '__main__':
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import small
    n, mask, goal, secs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    g, o = small.best(n, mask, 3)
    rows = [((1 << u) | (1 << (n + v))) for u in range(n) for v in range(n)]; R = len(rows)
    incols = [sum(1 << r for r in range(R) if rows[r] >> i & 1) for i in range(2 * n)]
    target = sum(1 << (u * n + v) for u in range(n) for v in range(n) if mask >> (n * u + v) & 1)
    t = time.time(); print('start', len(g), flush=True)
    g2, o2 = shrink(2 * n, incols, R, target, g, o, goal, secs)
    print('end', len(g2), 'after', round(time.time() - t), 's', evalc(2 * n, incols, g2)[o2] == target)
