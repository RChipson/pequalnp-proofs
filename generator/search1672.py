"""A faithful port of the frontier search of the checked 9-input certificate
(namespace Main1672, first accepted as L-meta-1672).  It is used to measure how
large the search is from a new starting frontier before any Lean is written.

Signals are pairs (p, n) of 414-bit integers; a wire is (p, n, tag).
Tags: 0 none, 1 deg3, 2 spec0, 3 spec1 (as Tag.toNat in the Lean file).
"""
import re, sys, time

NONE, DEG3, SPEC0, SPEC1 = 0, 1, 2, 3
BITS = 414
TOP = (1 << BITS) - 1
TARGET = (TOP, 0)

def load_raw(path):
    src = open(path).read()
    main = src[src.index('namespace Main1672'):]
    raw = []
    for j in range(9):
        m = re.search(r'def raw%d : Sig\s*:=\s*\((0x[0-9a-f]+|\d+),\s*(0x[0-9a-f]+|\d+)\)' % j, main)
        raw.append((int(m.group(1), 0), int(m.group(2), 0)))
    return raw

def sep0(p, n): return p & (n ^ TOP)
def sep1(p, n): return p ^ n

def cov_add(z, c):
    c1, c2, c3 = c
    return (z | c1, (z ^ c1) & (z | c2), c3 ^ (z & (c3 ^ c2)))

def take_one(c, a): return c[0] ^ (c[1] & a)
def take_two(c, a, b): return c[0] ^ ((c[1] & (a | b)) | (c[2] & (a & b)))

class Searcher:
    def __init__(self):
        self.memo = {}
        self.cost = {}
        self.acc = [0]

    def avail(self, g, v):
        if g == (0, 0) or g == (TOP, TOP): return False
        for w in v:
            if w[0] == g[0] and w[1] == g[1]: return False
        return True

    def search(self, k, t, v):
        """search k t v of the Lean file: can frontier v reach the target with
        at most k gates of which exactly t are NOT gates."""
        key = (k, t, frozenset(v))
        r = self.memo.get(key)
        if r is not None:
            self.acc[-1] += self.cost[key]
            return r
        self.acc.append(1)
        if k == 0:
            r = len(v) == 1 and (v[0][0], v[0][1]) == TARGET
        else:
            r = self.step(k - 1, t, v)
        c = self.acc.pop()
        self.cost[key] = c
        self.memo[key] = r
        self.acc[-1] += c
        return r

    def step(self, k, t, v):
        ln = len(v)
        if k + 1 < t or (k + 1 - t + 1) < ln: return False
        if ln == 1 and (v[0][0], v[0][1]) == TARGET: return True
        if t > 0 and self.unary(k, t - 1, ln, v): return True
        return self.binary(k, t, ln, v)

    def seps(self, d, v):
        c = (0, 0, 0)
        out = []
        for w in reversed(v):
            s = sep1(w[0], w[1]) if d else sep0(w[0], w[1])
            out.append((w, s))
            c = cov_add(s, c)
        out.reverse()
        return out, c

    def unary(self, k, t, ln, v):
        d = 0 if t == 0 else 1
        seps, c = self.seps(d, v)
        lim = k - t + 1
        n = ln - 1
        for (w, s) in seps:
            p, nn, tg = w
            if tg == SPEC0 or tg == SPEC1: continue
            gp, gn = p ^ TOP, nn ^ TOP
            base = (sep1(gp, gn) if d else sep0(gp, gn)) | take_one(c, s)
            ka = tg != DEG3 and n + 2 <= lim
            ok0 = base == TOP
            okA = ka and (base | s) == TOP
            if not (ok0 or okA): continue
            if not self.avail((gp, gn), v): continue
            gt = SPEC1 if tg == DEG3 else NONE
            rest = tuple(x for x in v if not (x[0] == p and x[1] == nn))
            g = (gp, gn, gt)
            if ok0 and self.search(k, t, (g,) + rest): return True
            if okA and self.search(k, t, (g, w) + rest): return True
        return False

    def binary(self, k, t, ln, v):
        lim = k - t + 1
        d = 0 if t == 0 else 1
        seps, c = self.seps(d, v)
        umask = c[1]
        mode = 0 if ln == lim + 1 else (1 if ln == lim else 2)
        acts = []
        for (w, s) in seps:
            u = umask & s
            acts.append((w, s, u, u & w[0], u & w[1]))
        m = len(acts)
        for i in range(m):
            for j in range(i + 1, m):
                if self.pair(k, t, d, mode, v, c, acts[i], acts[j]): return True
        return False

    def pair(self, k, t, d, mode, v, c, A, B):
        (wa, sa, ua, uap, uan) = A
        (wb, sb, ub, ubp, ubn) = B
        ap, an, atg = wa
        bp, bn, btg = wb
        t2 = take_two(c, sa, sb)
        rest = None
        # ---- AND
        if atg != SPEC0 and btg != SPEC0:
            if d == 0:
                usea = (ua & bp) == ua
                useb = (ub & ap) == ub
            else:
                usea = (uap & bp) == uap and (uan & bn) == uan
                useb = (ubp & ap) == ubp and (ubn & an) == ubn
            ka = atg == NONE
            kb = btg == NONE
            gp, gn = ap & bp, an & bn
            sg = sep1(gp, gn) if d else sep0(gp, gn)
            base = sg | t2
            gt = SPEC0 if (atg == DEG3 or btg == DEG3) else NONE
            g = (gp, gn, gt)
            if self.keeps(k, t, mode, v, base, sa, sb, g, wa, wb, ka, kb, usea, useb): return True
        # ---- OR
        if atg != SPEC1 and btg != SPEC1:
            if d == 0:
                usea = (ua & bn) == 0
                useb = (ub & an) == 0
            else:
                usea = (uap & bn) == 0 and (uan & bp) == 0
                useb = (ubp & an) == 0 and (ubn & ap) == 0
            ka = atg != SPEC0
            kb = btg != SPEC0
            gp, gn = ap | bp, an | bn
            sg = sep1(gp, gn) if d else sep0(gp, gn)
            base = sg | t2
            g = (gp, gn, NONE)
            wa2 = (ap, an, SPEC0 if atg == DEG3 else NONE)
            wb2 = (bp, bn, SPEC0 if btg == DEG3 else NONE)
            if self.keeps(k, t, mode, v, base, sa, sb, g, wa2, wb2, ka, kb, usea, useb): return True
        return False

    def keeps(self, k, t, mode, v, base, sa, sb, g, wa, wb, ka, kb, usea, useb):
        if mode == 0:
            if not (usea and useb): return False
            if base != TOP: return False
            if not self.avail((g[0], g[1]), v): return False
            rest = self.drop2(v, wa, wb)
            return self.search(k, t, (g,) + rest)
        if mode == 1:
            if not ((usea or useb) and (usea or ka) and (useb or kb)): return False
            ok0 = usea and useb and base == TOP
            okA = ka and useb and (base | sa) == TOP
            okB = kb and usea and (base | sb) == TOP
            if not (ok0 or okA or okB): return False
            if not self.avail((g[0], g[1]), v): return False
            rest = self.drop2(v, wa, wb)
            return ((ok0 and self.search(k, t, (g,) + rest)) or
                    (okA and self.search(k, t, (g, wa) + rest)) or
                    (okB and self.search(k, t, (g, wb) + rest)))
        if not ((ka or usea) and (kb or useb)): return False
        ok0 = base == TOP
        okA = ka and (base | sa) == TOP
        okB = kb and (base | sb) == TOP
        okAB = ka and kb and (base | sa | sb) == TOP
        if not (ok0 or okA or okB or okAB): return False
        if not self.avail((g[0], g[1]), v): return False
        rest = self.drop2(v, wa, wb)
        return ((ok0 and self.search(k, t, (g,) + rest)) or
                (okA and self.search(k, t, (g, wa) + rest)) or
                (okB and self.search(k, t, (g, wb) + rest)) or
                (okAB and self.search(k, t, (g, wa, wb) + rest)))

    @staticmethod
    def drop2(v, wa, wb):
        return tuple(x for x in v if not ((x[0] == wa[0] and x[1] == wa[1]) or (x[0] == wb[0] and x[1] == wb[1])))

def run(name, root, k, ts):
    """Report, for each NOT count t, whether the frontier `root` can reach the
    target within k gates (False is what a lower bound needs)."""
    for t in ts:
        s = Searcher()
        t0 = time.time()
        r = s.step(k - 1, t, tuple(root))
        per = {}; un = {}
        for key in s.memo:
            kk = key[0]
            per[kk] = per.get(kk, 0) + 1
            un[kk] = un.get(kk, 0) + s.cost[key]
        lv = ' '.join(f'{kk}:{per[kk]}/{un[kk]}' for kk in sorted(per, reverse=True))
        print(f'{name}: k={k} t={t} reachable={r} states={len(s.memo)} replay={1 + s.acc[0]} time={time.time()-t0:.1f}s level:states/replay {lv}', flush=True)
    return

if __name__ == '__main__':
    raw = load_raw(sys.argv[1])
    which = sys.argv[2] if len(sys.argv) > 2 else 'old'
    AND = lambda a, b: (a[0] & b[0], a[1] & b[1])
    OR = lambda a, b: (a[0] | b[0], a[1] | b[1])
    NOT = lambda a: (a[0] ^ TOP, a[1] ^ TOP)
    def wires(tags, extra=()):
        return [raw[j] + (tg,) for j, tg in tags.items()] + list(extra)
    if which == 'old':
        tags = {j: (SPEC0 if j in (4, 6, 7) else DEG3) for j in range(9)}
        run('old root', wires(tags), 14, range(0, 7))
    elif which == '3120_6':
        sA = AND(raw[0], raw[3]); n6 = NOT(raw[6])
        tags = {0: DEG3, 1: NONE, 2: NONE, 3: DEG3, 4: DEG3, 5: NONE, 7: DEG3, 8: NONE}
        run('3120 i=6 both used', wires(tags, [sA + (DEG3,), n6 + (SPEC1,)]), 13, range(0, 5))
    elif which == '3120':
        sA = AND(raw[0], raw[3])
        allS0 = {j: SPEC0 for j in range(9)}
        run('(a) raw at 13', wires(allS0), 13, range(0, 6))
        for i in (6, 5):
            ni = NOT(raw[i])
            tg = {j: (SPEC0 if j in (4, 6, 7) else DEG3) for j in range(9) if j != i}
            run(f'(c) i={i} raw without raw{i}, with its negation', wires(tg, [ni + (SPEC1,)]), 13, range(0, 6))
        tg = {0: DEG3, 1: NONE, 2: NONE, 3: DEG3, 4: DEG3, 5: NONE, 7: DEG3, 8: NONE}
        n6 = NOT(raw[6])
        run('(d) i=6 without raw6', wires(tg, [sA + (DEG3,), n6 + (SPEC1,)]), 13, range(0, 5))
        tg[6] = SPEC0
        run('(d) i=6 with raw6', wires(tg, [sA + (DEG3,), n6 + (SPEC1,)]), 13, range(0, 4))
        tg = {0: DEG3, 1: NONE, 2: NONE, 3: DEG3, 4: DEG3, 6: DEG3, 7: DEG3, 8: NONE}
        n5 = NOT(raw[5])
        run('(d) i=5 without raw5', wires(tg, [sA + (DEG3,), n5 + (NONE,)]), 13, range(0, 5))
        tg[5] = DEG3
        run('(d) i=5 with raw5', wires(tg, [sA + (DEG3,), n5 + (NONE,)]), 13, range(0, 4))
    elif which == 'notfirst':
        # first gate NOT x_i, 14 further gates (steps 1665, 1666, 3271)
        n4 = NOT(raw[4]); n0 = NOT(raw[0])
        tg = {0: NONE, 1: NONE, 2: NONE, 3: NONE, 5: NONE, 6: DEG3, 7: DEG3, 8: NONE}
        run('1666: raw without raw4, with its negation', wires(tg, [n4 + (SPEC1,)]), 14, range(0, 7))
        tg = {1: NONE, 2: NONE, 3: NONE, 4: DEG3, 5: NONE, 6: DEG3, 7: DEG3, 8: NONE}
        run('1665/3271: raw without raw0, with its negation', wires(tg, [n0 + (NONE,)]), 14, range(0, 7))
    elif which == 'plain':
        # no tags at all: the nine inputs, K gates (third argument), each NOT count
        K = int(sys.argv[3]); ts = [int(x) for x in sys.argv[4].split(',')]
        run(f'plain root K={K}', wires({j: NONE for j in range(9)}), K, ts)
    elif which == '3138':
        o = OR(raw[0], raw[3])
        tags = {0: DEG3, 1: NONE, 2: NONE, 3: DEG3, 4: DEG3, 5: NONE, 6: DEG3, 7: DEG3, 8: NONE}
        run('3138 or03 used', wires(tags, [o + (NONE,)]), 14, range(0, 2))
