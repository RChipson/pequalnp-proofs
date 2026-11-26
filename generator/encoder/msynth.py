#!/usr/bin/env python3
"""Exact search (SAT, cadical) for a monotone circuit (AND/OR gates of fan-in two) on given input rows that
has, among its gate wires, every one of a list of target columns.

  rows: the inputs are wires 0..n-1; row r gives every input a value.
  A column is a number whose bit r is the value on row r.

search(n, incols, targets, G, ops, seconds) -> list of gates (op, a, b) and the target wires, or None/'timeout'.
ops: 'or' (OR gates only) or 'andor'."""
import itertools, os, subprocess, sys, tempfile

def search(n, incols, R, targets, G, ops='andor', seconds=600, seed=0, extra=None):
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cl = []
    v = [[new() for r in range(R)] for g in range(G)]
    op = [new() for g in range(G)] if ops == 'andor' else None     # true = AND
    sa = []; sb = []
    A = [[new() for r in range(R)] for g in range(G)]
    B = [[new() for r in range(R)] for g in range(G)]
    def val(j, r):
        """literal or constant for wire j at row r"""
        if j < n: return True if incols[j] >> r & 1 else False
        return v[j - n][r]
    for g in range(G):
        W = n + g
        a = [new() for j in range(W)]; b = [new() for j in range(W)]
        sa.append(a); sb.append(b)
        cl.append(a[:]); cl.append(b[:])
        for i in range(W):
            for j in range(i + 1, W): cl.append([-a[i], -a[j]]); cl.append([-b[i], -b[j]])
        # a's wire is below b's wire
        for i in range(W):
            for j in range(0, i + 1): cl.append([-a[i], -b[j]])
        for j in range(W):
            for r in range(R):
                x = val(j, r)
                for sel, T in ((a[j], A[g][r]), (b[j], B[g][r])):
                    if x is True: cl.append([-sel, T])
                    elif x is False: cl.append([-sel, -T])
                    else: cl.append([-sel, -T, x]); cl.append([-sel, T, -x])
        for r in range(R):
            y, p, q = v[g][r], A[g][r], B[g][r]
            if ops == 'or':
                cl.append([-y, p, q]); cl.append([y, -p]); cl.append([y, -q])
            else:
                o = op[g]
                # OR when o false
                cl.append([o, -y, p, q]); cl.append([o, y, -p]); cl.append([o, y, -q])
                # AND when o true
                cl.append([-o, y, -p, -q]); cl.append([-o, -y, p]); cl.append([-o, -y, q])
    ts = []
    for t in targets:
        s = [new() for g in range(G)]; ts.append(s); cl.append(s[:])
        for g in range(G):
            for r in range(R):
                cl.append([-s[g], v[g][r] if t >> r & 1 else -v[g][r]])
    # every gate except the last is read by a later gate or is a target (no dead gates)
    for g in range(G):
        users = [sa[h][n + g] for h in range(g + 1, G)] + [sb[h][n + g] for h in range(g + 1, G)] + [s[g] for s in ts]
        cl.append(users)
    if extra: cl += extra(locals())
    fd, path = tempfile.mkstemp(suffix='.cnf'); os.close(fd)
    with open(path, 'w') as f:
        f.write('p cnf %d %d\n' % (nv[0], len(cl)))
        for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
    try:
        r = subprocess.run(['cadical', '-q', '-t', str(int(seconds)), '--seed=%d' % seed, path], capture_output=True, text=True)
    finally:
        os.unlink(path)
    if r.returncode == 20: return None
    if r.returncode != 10: return 'timeout'
    model = set()
    for line in r.stdout.split('\n'):
        if line.startswith('v'):
            for x in line.split()[1:]:
                if int(x) > 0: model.add(int(x))
    gates = []
    for g in range(G):
        a = [j for j in range(n + g) if sa[g][j] in model][0]; b = [j for j in range(n + g) if sb[g][j] in model][0]
        gates.append(('and' if ops == 'andor' and op[g] in model else 'or', a, b))
    outs = [n + [g for g in range(G) if s[g] in model][0] for s in ts]
    return gates, outs

def check(n, incols, R, targets, gates, outs):
    W = list(incols)
    for o, a, b in gates: W.append(W[a] & W[b] if o == 'and' else W[a] | W[b])
    return all(W[w] == t for w, t in zip(outs, targets))

if __name__ == '__main__':
    k = int(sys.argv[1]); G = int(sys.argv[2]); neg = sys.argv[3] == 'neg'; ops = sys.argv[4]; secs = int(sys.argv[5])
    n = 1 << k
    incols = [1 << p for p in range(n)]
    targets = [sum(1 << p for p in range(n) if p >> b & 1) for b in range(k)]
    if neg: targets += [sum(1 << p for p in range(n) if not p >> b & 1) for b in range(k)]
    res = search(n, incols, n, targets, G, ops, secs)
    print(k, G, 'neg' if neg else 'plain', ops, '->', res if not isinstance(res, tuple) else ('FOUND', check(n, incols, n, targets, *res), res))
