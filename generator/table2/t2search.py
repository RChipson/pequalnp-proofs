# A Python copy of the search that the Lean file runs in the kernel, with a cost count.
# It serves two ends: to see before any Lean run that every row closes, and to cut heavy rows
# into pieces small enough for the memory limit.
import t2lib
from t2lib import R, W, F256
C = t2lib.CONSTS
FU, cH, cL, cM, cO, cB, cC = C['FU'], C['cH'], C['cL'], C['cM'], C['cO'], C['cB'], C['cC']
SH = 16384

def nz(X): return (((X & cL) + cL) | X) & cH
def flag(Y): return (cH ^ Y) >> 255
def pbits(X): return nz(X) & nz(X ^ FU)
_ind = {}
def ind(X):
    r = _ind.get(X)
    if r is None:
        r = _ind[X] = flag(pbits(X))
    return r
def ncb(G, A, B): return pbits(G) & nz(G ^ A) & nz(G ^ B)
_sep = {}
def sepv(X):
    r = _sep.get(X)
    if r is None:
        r = _sep[X] = (X ^ (X >> SH)) & cC
    return r
def cmpX(Rv, X): return ((Rv + X + cO) & cB) == cB
def dig(r, X): return (X >> (W * r)) & F256

class Row:
    def __init__(self, tab, i, PI):
        self.i = i
        g, V, rank = tab[i]
        self.g, self.V, self.rank = g, V, rank
        self.T = T = t2lib.pack(g)
        self.sens = sens = sepv(T)
        index = {h: j for j, (h, _, _) in enumerate(tab)}
        ov = []
        for r in range(R):
            j = index.get(dig(r, T))
            ov.append(tab[j][1] if j is not None and tab[j][2] < rank else 0)
        def nec(X):
            u = 0
            for Y in PI:
                if Y != X: u |= sepv(Y)
            return (u & sens) != sens
        self.v0 = [X for X in PI if nec(X)]
        self.lv0 = sum(o << (W * r) for r, o in enumerate(ov)) + sum(ind(X) for X in self.v0)
        self.nu = sum((150 if o == 0 else 0) << (W * r) for r, o in enumerate(ov))
        self.pre_ok = (T != 0 and T != FU and
                       all(nec(PI[j]) or dig(1 + j, T) == g for j in range(8)))
    def root(self, k):
        return (self.v0, self.lv0, k * cO + self.nu, 0)

def tests(v):
    out = [(a, a, a ^ FU, True) for a in v]
    for x in range(len(v)):
        for y in range(x + 1, len(v)):
            a, b = v[x], v[y]
            out.append((a, b, a & b, False))
            out.append((a, b, a | b, False))
    return out

def del_of(d, a, b):
    return [[], [a], [b], [a, b]][d]

class Search:
    def __init__(self, row):
        self.y, self.sens = row.T, row.sens
        self.cost = 0
        self.found = False
    def pre(self, st, t):
        a, b, G, un = t
        prev = st[3]
        return G != 0 and G != FU and G != a and G != b and (a == prev or b == prev or prev < G)
    def kid(self, st, t, d):
        v, Lv, Rv, prev = st
        a, b, G, un = t
        dl = del_of(d, a, b)
        return ([G] + [x for x in v if x not in dl], Lv + flag(ncb(G, a, b)) + ind(G),
                Rv + sum(ind(x) for x in dl), G)
    def guard(self, k, st, t, d, Lv2):
        # the three cheap tests of one disposal; k is the number of steps left after this gate
        v, Lv, Rv, prev = st
        a, b, G, un = t
        if un and d >= 2: return False
        dl = del_of(d, a, b)
        if len(v) + 1 > k + 1 + len(dl): return False
        u = sepv(G)
        for x in v:
            if x not in dl: u |= sepv(x)
        if (u & self.sens) != self.sens: return False
        return cmpX(Rv + sum(ind(x) for x in dl), Lv2 ^ cM)
    def tryT(self, k, st, t, d):
        a, b, G, un = t
        Lv2 = st[1] + flag(ncb(G, a, b)) + ind(G)
        if not self.guard(k, st, t, d, Lv2): return False
        return self.search(k, self.kid(st, t, d))
    def cand(self, k, st, t):
        if not self.pre(st, t): return False
        self.cost += 1
        a, b, G, un = t
        Lv2 = st[1] + flag(ncb(G, a, b)) + ind(G)
        for d in range(2 if un else 4):
            if self.guard(k, st, t, d, Lv2) and self.search(k, self.kid(st, t, d)):
                return True
        return False
    def search(self, k, st):
        # k steps left from the state st
        if k == 0:
            r = (len(st[0]) == 1 and st[0][0] == self.y)
            if r: self.found = True
            return r
        for t in tests(st[0]):
            if self.cand(k - 1, st, t): return True
        return False

def row_cost(row):
    # (closes, list of (k, cost)) over all k below the bound
    out = []
    ok = row.pre_ok
    for k in range(row.V):
        st = row.root(k)
        s = Search(row)
        if len(row.v0) <= k + 1 and cmpX(st[2], st[1] ^ cM):
            if s.search(k, st): ok = False
        out.append((k, s.cost))
    return ok, out
