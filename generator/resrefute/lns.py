#!/usr/bin/env python3
"""Shorten a resolution refutation of the pigeonhole formula by re-deriving small parts of it with a
SAT solver (large-neighbourhood search).

A window W is a set of derived lines.  Its targets are the lines of W read from outside W (and the
empty clause if it is in W).  The solver is asked to derive every target from the lines that do not
depend on W with |W| - 1 resolvents.  A yes replaces W and the refutation is one line shorter.

  python3 lns.py <start.json> <out.json> <seconds> [seed] [window size] [seconds per window]
  python3 lns.py parse171 <lean file> <m> <n> <out.json>      read the certificate of a proof in the L-pcx-171 format"""
import itertools, json, os, random, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import resenc, genres

def parse171(path, m, n):
    src = open(path).read(); a = src.index('def cert'); b = src.index(']\n', a)
    ent = []
    for line in src[a:b + 1].split('\n')[1:]:
        line = line.strip().rstrip(',')
        if not line.startswith('('): continue
        mm = re.match(r'\((∅|\{.*?\}), (none|some \((\d+), (\d+), \((\d+), (\d+)\)\))\)\]?$', line)
        assert mm, line
        cl = [] if mm.group(1) == '∅' else [2 * (int(p) * n + int(h)) + (0 if s == 'true' else 1) for p, h, s in re.findall(r'\(\((\d+), (\d+)\), (true|false)\)', mm.group(1))]
        ent.append((sorted(cl), None if mm.group(2) == 'none' else (int(mm.group(3)), int(mm.group(4)), int(mm.group(5)) * n + int(mm.group(6)))))
    N = len(ent); lines = [None] * N; hints = [None] * N
    for p, (cl, h) in enumerate(ent):            # position p (newest first) is line r = N - 1 - p
        r = N - 1 - p; lines[r] = cl
        if h is not None:
            i, j, v = h; hints[r] = (r - 1 - i, r - 1 - j, v)
    return lines, hints

def normalise(m, n, lines, hints):
    """Keep only lines the first empty clause depends on; axioms first, then resolvents in order."""
    e = next(i for i, c in enumerate(lines) if len(c) == 0)
    need = set(); st = [e]
    while st:
        x = st.pop()
        if x in need: continue
        need.add(x)
        if hints[x] is not None: st += [hints[x][0], hints[x][1]]
    order = [i for i in sorted(need) if hints[i] is None] + [i for i in sorted(need) if hints[i] is not None]
    pos = {o: k for k, o in enumerate(order)}
    L = [lines[o] for o in order]; H = [None if hints[o] is None else (pos[hints[o][0]], pos[hints[o][1]], hints[o][2]) for o in order]
    return L, H

def try_window(m, n, lines, hints, W, seconds, seed):
    N = len(lines); NV = m * n; NL = 2 * NV; Wset = set(W)
    desc = set(Wset)
    for r in range(N):
        if hints[r] is not None and (hints[r][0] in desc or hints[r][1] in desc): desc.add(r)
    src = [r for r in range(N) if r not in desc]
    readers_out = {w for r in range(N) if r not in Wset and hints[r] is not None for w in (hints[r][0], hints[r][1]) if w in Wset}
    targets = sorted(readers_out | {w for w in W if len(lines[w]) == 0})
    k = len(W) - 1
    if k < len(targets) or k < 1: return None
    nv = [0]; cls = []
    def new():
        nv[0] += 1; return nv[0]
    S = len(src)
    L = [[new() for _ in range(NL)] for _ in range(k)]
    s1 = [[new() for _ in range(S + r)] for r in range(k)]; s2 = [[new() for _ in range(S + r)] for r in range(k)]
    pv = [[new() for _ in range(NV)] for _ in range(k)]
    Aa = [[new() for _ in range(NL)] for _ in range(k)]; Bb = [[new() for _ in range(NL)] for _ in range(k)]
    srcset = [set(lines[x]) for x in src]
    def lit(i, l): return (l in srcset[i]) if i < S else L[i - S][l]
    for r in range(k):
        for sel in (s1[r], s2[r], pv[r]):
            cls.append(list(sel))
            for a, b in itertools.combinations(sel, 2): cls.append([-a, -b])
        for sel, X in ((s1[r], Aa[r]), (s2[r], Bb[r])):
            for i in range(S + r):
                for l in range(NL):
                    w = lit(i, l)
                    if w is True: cls.append([-sel[i], X[l]])
                    elif w is False: cls.append([-sel[i], -X[l]])
                    else: cls.append([-sel[i], -X[l], w]); cls.append([-sel[i], X[l], -w])
        for v in range(NV):
            p = pv[r][v]; a0, a1, b0, b1 = Aa[r][2 * v], Aa[r][2 * v + 1], Bb[r][2 * v], Bb[r][2 * v + 1]; l0, l1 = L[r][2 * v], L[r][2 * v + 1]
            cls += [[-p, a0], [-p, b1], [-l0, a0, b0], [-l0, -p, b0], [l0, -a0, p], [l0, -b0], [-l1, a1, b1], [-l1, a1, -p], [l1, -a1], [l1, -b1, p], [-l0, -l1]]
    eq = {}
    for t in targets:
        row = []
        for r in range(k):
            e = new(); row.append(e)
            tl = set(lines[t])
            for l in range(NL): cls.append([-e, L[r][l] if l in tl else -L[r][l]])
        cls.append(row); eq[t] = row
    for r in range(k):      # every new line is read later or is a target
        cls.append([s1[q][S + r] for q in range(r + 1, k)] + [s2[q][S + r] for q in range(r + 1, k)] + [eq[t][r] for t in targets])
    cnf = f'/tmp/lns_{os.getpid()}.cnf'
    with open(cnf, 'w') as f:
        f.write(f'p cnf {nv[0]} {len(cls)}\n'); f.write('\n'.join(' '.join(map(str, c)) + ' 0' for c in cls) + '\n')
    try:
        out = subprocess.run(['cadical', '-q', f'--seed={seed}', '-t', str(int(seconds)), cnf], capture_output=True, text=True, timeout=seconds + 30).stdout
    except subprocess.TimeoutExpired:
        return None
    if 's SATISFIABLE' not in out: return None
    mod = set()
    for line in out.split('\n'):
        if line.startswith('v '): mod |= {int(x) for x in line.split()[1:] if int(x) > 0}
    # rebuild: sources (old indices), then the new lines, then the lines that depended on W
    newl = []; newh = []
    for r in range(k):
        i = next(x for x in range(S + r) if s1[r][x] in mod); j = next(x for x in range(S + r) if s2[r][x] in mod); v = next(x for x in range(NV) if pv[r][x] in mod)
        newl.append(sorted(l for l in range(NL) if L[r][l] in mod)); newh.append((i, j, v))
    tpos = {t: S + next(r for r in range(k) if eq[t][r] in mod) for t in targets}
    rest = [r for r in range(N) if r in desc and r not in Wset]
    idx = {x: a for a, x in enumerate(src)}
    idx.update(tpos)
    for a, x in enumerate(rest): idx[x] = S + k + a
    lines2 = [lines[x] for x in src] + newl + [lines[x] for x in rest]
    hints2 = [None if hints[x] is None else (idx[hints[x][0]], idx[hints[x][1]], hints[x][2]) for x in src] + newh + \
             [(idx[hints[x][0]], idx[hints[x][1]], hints[x][2]) for x in rest]
    return lines2, hints2

def pick_window(lines, hints, rnd, size):
    N = len(lines); derived = [r for r in range(N) if hints[r] is not None]
    t = rnd.choice(derived); W = [t]; frontier = [t]
    while frontier and len(W) < size:
        x = frontier.pop(rnd.randrange(len(frontier)))
        for p in (hints[x][0], hints[x][1]):
            if hints[p] is not None and p not in W and len(W) < size: W.append(p); frontier.append(p)
    return W

def main():
    if sys.argv[1] == 'parse171':
        m, n = int(sys.argv[3]), int(sys.argv[4]); lines, hints = parse171(sys.argv[2], m, n)
        lines, hints = normalise(m, n, lines, hints); genres.check(m, n, lines, hints)
        json.dump(dict(m=m, n=n, lines=lines, hints=hints), open(sys.argv[5], 'w')); print('parsed', len(lines), 'lines'); return
    d = json.load(open(sys.argv[1])); m, n = d['m'], d['n']; out = sys.argv[2]; secs = float(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1; size = int(sys.argv[5]) if len(sys.argv) > 5 else 12; per = float(sys.argv[6]) if len(sys.argv) > 6 else 40
    rnd = random.Random(seed); lines, hints = normalise(m, n, d['lines'], d['hints']); genres.check(m, n, lines, hints)
    t0 = time.time(); tries = 0
    print('start', len(lines), 'lines', flush=True)
    while time.time() - t0 < secs:
        tries += 1
        W = pick_window(lines, hints, rnd, rnd.randint(max(4, size - 6), size))
        res = try_window(m, n, lines, hints, W, per, rnd.randrange(1 << 20))
        if res:
            l2, h2 = normalise(m, n, *res); genres.check(m, n, l2, h2)
            if len(l2) < len(lines):
                lines, hints = l2, h2
                json.dump(dict(m=m, n=n, lines=lines, hints=hints), open(out, 'w'))
                print(f'{len(lines)} lines after {tries} windows, {int(time.time() - t0)} s', flush=True)
    print('end', len(lines), 'lines after', tries, 'windows', flush=True)

if __name__ == '__main__':
    main()
