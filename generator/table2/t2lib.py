# Shared data layer for the Table 2 generator: block layout, packing, the table of restrictions.
import itertools
R = 129
W = 256
NS = R * W
F256 = (1 << 256) - 1

def layout():
    # block -> list of (input, value); block 0 is the identity
    rho = [[] for _ in range(R)]
    for i in range(8):
        rho[1 + i] = [(i, 0)]
        rho[65 + i] = [(i, 1)]
    t = 0
    for i in range(8):
        for j in range(i + 1, 8):
            rho[9 + t] = [(i, 0), (j, 0)]
            rho[73 + t] = [(i, 1), (j, 1)]
            rho[37 + t] = [(i, 0), (j, 1)]
            rho[101 + t] = [(i, 1), (j, 0)]
            t += 1
    return rho
RHO = layout()

def mi(i):
    return sum(1 << p for p in range(256) if not (p >> i) & 1)
MI = [mi(i) for i in range(8)]

def p1(i, c, x):
    low = (x >> (c << i)) & MI[i]
    return low | (low << (1 << i))

def prj(r, x):
    for (i, c) in RHO[r]:
        x = p1(i, c, x)
    return x & F256

def pack(x):
    return sum(prj(r, x) << (W * r) for r in range(R))

def rep(c):
    return sum(c << (W * r) for r in range(R))

def rcodes():
    def code(kind, i=0, ci=0, j=0, cj=0):
        return kind + 4 * i + 32 * ci + 64 * j + 512 * cj
    out = []
    for r in range(R):
        rr = RHO[r]
        if len(rr) == 0: out.append(0)
        elif len(rr) == 1: out.append(code(1, rr[0][0], rr[0][1]))
        else: out.append(code(2, rr[0][0], rr[0][1], rr[1][0], rr[1][1]))
    return sum(c << (16 * r) for r, c in enumerate(out))

CONSTS = {
    'FU': (1 << NS) - 1,
    'cH': rep(1 << 255),
    'cL': rep((1 << 255) - 1),
    'cM': rep(255),
    'cO': rep(1),
    'cB': rep(256),
    'cC': sum(F256 << (W * r) for r in range(1, 65)),
    'cMT': sum(MI[i] << (256 * i) for i in range(8)),
    'cRT': rcodes(),
}

XT = [F256 ^ MI[i] for i in range(8)]   # truth table of input i

def edge_table(E):
    t = 0
    for p in range(256):
        if any((p >> a) & 1 and (p >> b) & 1 for a, b in E):
            t |= 1 << p
    return t

def deps(g):
    return [i for i in range(8) if (g ^ (g >> (1 << i))) & MI[i]]

def formula(g):
    # value of a restriction of a graph function: free inputs A joined by OR with an edge function
    A = [a for a in range(8) if (g >> (1 << a)) & 1]
    E2 = [(a, b) for a in range(8) for b in range(a + 1, 8)
          if a not in A and b not in A and (g >> ((1 << a) | (1 << b))) & 1]
    chk = 0
    for p in range(256):
        if any((p >> a) & 1 for a in A) or any((p >> a) & 1 and (p >> b) & 1 for a, b in E2):
            chk |= 1 << p
    assert chk == g, 'not a graph restriction'
    if not E2:
        return max(len(A) - 1, 0)
    tau = min(len(c) for k in range(9) for c in itertools.combinations(range(8), k)
              if all(a in c or b in c for a, b in E2))
    return len(A) + len(E2) + tau - 1

def build_table(E, values=None):
    # all non-constant restrictions reachable through the blocks, with value and rank
    root = edge_table(E)
    seen = {}
    todo = [root]
    while todo:
        g = todo.pop()
        if g in seen: continue
        d = len(deps(g))
        seen[g] = d
        for r in range(1, R):
            h = prj(r, g)
            if h == 0 or h == F256: continue
            if len(deps(h)) < d and h not in seen:
                todo.append(h)
    keys = sorted(seen)
    tab = []
    for g in keys:
        V = formula(g) if values is None else values[g]
        assert 0 <= V < 16 and seen[g] < 16
        tab.append((g, V, seen[g]))
    return root, tab

# ---- the table as Lean data: keys in chunks, and a two-choice hash index ----
KCH = 32      # keys in one chunk
HCH = 64      # slots in one chunk of a hash table
HM = 1024     # slots in one hash table

def cuckoo(keys):
    import random
    primes = [1000003, 1000033, 1000037, 1000039, 1000081, 1000099, 1000117, 1000121, 1000133, 1000151]
    rnd = random.Random(1)
    for p1 in primes:
        for p2 in primes:
            if p1 == p2: continue
            t = [[0] * HM, [0] * HM]
            ok = True
            for j, g in enumerate(keys):
                cur, side = j, 0
                for _ in range(200):
                    h = (keys[cur] % (p1 if side == 0 else p2)) % HM
                    if t[side][h] == 0:
                        t[side][h] = cur + 1; cur = None; break
                    t[side][h], cur = cur + 1, t[side][h] - 1
                    side ^= 1
                if cur is not None:
                    ok = False; break
            if ok:
                return p1, p2, t
    raise SystemExit('no hash index found')

def sel_def(name, chunks):
    lines = [f'def {name} : Nat → Nat']
    for c, v in enumerate(chunks):
        lines.append(f'  | {c} => {hex(v)}')
    lines.append('  | _ => 0')
    return '\n'.join(lines) + '\n'

def table_data(tab, root):
    keys = [g for g, _, _ in tab]
    N = len(keys)
    i0 = keys.index(root)
    p1, p2, t = cuckoo(keys)
    kch = [sum(keys[c * KCH + x] << (256 * x) for x in range(KCH) if c * KCH + x < N)
           for c in range((N + KCH - 1) // KCH)]
    def hch(tt):
        return [sum(tt[c * HCH + x] << (10 * x) for x in range(HCH)) for c in range(HM // HCH)]
    vr = sum((v + 16 * r) << (8 * i) for i, (g, v, r) in enumerate(tab))
    s = sel_def('kc', kch) + '\n' + sel_def('hs1', hch(t[0])) + '\n' + sel_def('hs2', hch(t[1])) + '\n'
    s += f'def cP1 : Nat := {p1}\n\ndef cP2 : Nat := {p2}\n\n'
    s += f'def cN : Nat := {N}\n\ndef cVR : Nat := {hex(vr)}\n\ndef cI0 : Nat := {i0}\n'
    return s, N, i0
