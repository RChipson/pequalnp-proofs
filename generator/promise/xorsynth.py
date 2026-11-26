#!/usr/bin/env python3
"""Fast search for promise rows: a circuit of the shape  F xor G  (or F and not G, or F or not G), where
F and G are wires of one small AND/OR circuit.  The XOR costs four gates (OR, AND, NOT, AND), the other
two shapes cost two.  As in unread.py, classes of equal rows / columns may be left unread.

find(n, mask, k, seconds) -> gate list on the original wire numbers (format of synth_not), or None."""
import itertools, os, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mux'))
import synth_not, unread

def mono_two(nin, rows, G, shape, seconds):
    """rows: list of (input bits, wanted output).  Monotone circuit with G gates and two chosen wires F, G2."""
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cl = []; R = len(rows)
    v = [[new() for r in range(R)] for g in range(G)]
    op = [new() for g in range(G)]; sa = []; sb = []
    def val(j, r): return bool(rows[r][0] >> j & 1) if j < nin else v[j - nin][r]
    for g in range(G):
        W = nin + g
        a = [new() for j in range(W)]; b = [new() for j in range(W)]; sa.append(a); sb.append(b)
        cl.append(a[:]); cl.append(b[:])
        for i in range(W):
            for j in range(i + 1, W): cl.append([-a[i], -a[j]]); cl.append([-b[i], -b[j]])
            for j in range(0, i + 1): cl.append([-a[i], -b[j]])
        for r in range(R):
            A = new(); B = new()
            for j in range(W):
                x = val(j, r)
                for sel, T in ((a[j], A), (b[j], B)):
                    if x is True: cl.append([-sel, T])
                    elif x is False: cl.append([-sel, -T])
                    else: cl.append([-sel, -T, x]); cl.append([-sel, T, -x])
            y, o = v[g][r], op[g]
            cl += [[o, -y, A, B], [o, y, -A], [o, y, -B], [-o, y, -A, -B], [-o, -y, A], [-o, -y, B]]
    W = nin + G
    fs = [new() for j in range(W)]; gs = [new() for j in range(W)]
    for sel in (fs, gs):
        cl.append(sel[:])
        for i in range(W):
            for j in range(i + 1, W): cl.append([-sel[i], -sel[j]])
    for r in range(R):
        Fv = new(); Gv = new()
        for j in range(W):
            x = val(j, r)
            for sel, T in ((fs[j], Fv), (gs[j], Gv)):
                if x is True: cl.append([-sel, T])
                elif x is False: cl.append([-sel, -T])
                else: cl.append([-sel, -T, x]); cl.append([-sel, T, -x])
        want = rows[r][1]
        if shape == 'xor':
            cl += ([[Fv, Gv], [-Fv, -Gv]] if want else [[-Fv, Gv], [Fv, -Gv]])
        elif shape == 'andnot':
            cl += ([[Fv], [-Gv]] if want else [[-Fv, Gv]])
        elif shape == 'ornot':
            cl += ([[Fv, -Gv]] if want else [[-Fv], [Gv]])
    for g in range(G):
        cl.append([sa[h][nin + g] for h in range(g + 1, G)] + [sb[h][nin + g] for h in range(g + 1, G)] + [fs[nin + g], gs[nin + g]])
    # neighbouring independent gates in order (see synth_not)
    for g in range(G - 1):
        Wg = nin + g; u = [sa[g + 1][Wg], sb[g + 1][Wg]]
        for i in range(Wg):
            for j in range(i): cl.append(u + [-sb[g][i], -sb[g + 1][j]])
            for p in range(Wg):
                for q in range(p): cl.append(u + [-sb[g][i], -sb[g + 1][i], -sa[g][p], -sa[g + 1][q]])
    fd, path = tempfile.mkstemp(suffix='.cnf'); os.close(fd)
    with open(path, 'w') as f:
        f.write('p cnf %d %d\n' % (nv[0], len(cl)))
        for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
    try: r = subprocess.run(['cadical', '-q', '-t', str(int(max(1, seconds))), path], capture_output=True, text=True)
    finally: os.unlink(path)
    if r.returncode != 10: return None if r.returncode == 20 else 'timeout'
    model = set()
    for line in r.stdout.split('\n'):
        if line.startswith('v'): model.update(int(x) for x in line.split()[1:] if int(x) > 0)
    gates = []
    for g in range(G):
        a = [j for j in range(nin + g) if sa[g][j] in model][0]; b = [j for j in range(nin + g) if sb[g][j] in model][0]
        gates.append(('and' if op[g] in model else 'or', a, b))
    return gates, [j for j in range(W) if fs[j] in model][0], [j for j in range(W) if gs[j] in model][0]

def find(n, mask, k, seconds, verbose=False, shapes=('andnot', 'ornot', 'xor')):
    """Smallest first: for each number of AND/OR gates, each shape, with and without unread twin classes."""
    rc, cc = unread.classes(n, mask)
    tr = [c for c in rc if len(c) > 1]; tc = [c for c in cc if len(c) > 1]
    skips = [([], [])]
    if tr or tc: skips.append((tr[0] if tr else [], tc[0] if tc else []))
    over = {'xor': 4, 'andnot': 2, 'ornot': 2}
    t_end = time.time() + seconds
    dead = set()
    for total in range(4, k + 1):
        for shape in shapes:
            G = total - over[shape]
            if G < 1: continue
            for sr, sc in skips:
                if (shape, tuple(sr), tuple(sc)) in dead: continue
                keep = [i for i in range(n) if i not in sr] + [n + j for j in range(n) if j not in sc]
                pos = {w: i for i, w in enumerate(keep)}; seen = set(); rows = []
                for u in range(n):
                    for v in range(n):
                        x = (0 if u in sr else 1 << pos[u]) | (0 if v in sc else 1 << pos[n + v])
                        o = bool(mask >> (n * u + v) & 1)
                        if (x, o) not in seen: seen.add((x, o)); rows.append((x, o))
                left = t_end - time.time()
                if left <= 1: return None
                res = mono_two(len(keep), rows, G, shape, left)
                if verbose: print(total, shape, sr, sc, 'found' if isinstance(res, tuple) else res, round(time.time() - t_end + seconds, 1), flush=True)
                if res == 'timeout': return None
                if not isinstance(res, tuple): continue
                mg, F, G2 = res; m = len(keep)
                w = lambda i: keep[i] if i < m else 2 * n + (i - m)
                gates = [(t, w(a), w(b)) for t, a, b in mg]; base = 2 * n + len(gates); f, g2 = w(F), w(G2)
                if shape == 'xor': gates += [('or', min(f, g2), max(f, g2)), ('and', min(f, g2), max(f, g2)), ('not', base + 1, base + 1), ('and', base, base + 2)]
                elif shape == 'andnot': gates += [('not', g2, g2), ('and', min(f, base), max(f, base))]
                else: gates += [('not', g2, g2), ('or', min(f, base), max(f, base))]
                if unread.check(n, mask, gates): return gates
    return None

if __name__ == '__main__':
    n, mask, k, secs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    t = time.time(); g = find(n, mask, k, secs, True)
    print(n, mask, k, ('CIRCUIT ' + repr(g)) if g else 'none', round(time.time() - t, 1))
