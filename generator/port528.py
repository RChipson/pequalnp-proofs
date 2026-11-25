#!/usr/bin/env python3
"""Port the accepted search proof L-meta-528 (8 inputs, at least 10 gates, AND/OR/NOT) to another
8-vertex graph.

Usage: port528.py <step id, e.g. L-meta-6606> <statement file> <out file> <edges, e.g. 0-1 0-2 ...>

The rows of the search are the sensitive pairs of the graph's edge function (a false input and the
true input one bit above it). Before writing the file, the search is replayed here in Python; the
file is written only if every root of the search comes back false, as the Lean proof needs.
The edges must be given in the order the statement lists them.
"""
import re, subprocess, sys

def main():
    step, stmt_file, out = sys.argv[1], sys.argv[2], sys.argv[3]
    E = [tuple(int(v) for v in e.split('-')) for e in sys.argv[4:]]
    ident = step.replace('-', '_')
    src = subprocess.run(['git', 'show', 'upstream/main:lean/PEqualNP/Outside/L_meta_528.lean'],
                         capture_output=True, text=True, check=True).stdout
    f = lambda x: any(x >> a & 1 and x >> b & 1 for a, b in E)
    pairs = [(x, i) for x in range(256) for i in range(8)
             if not f(x) and not x >> i & 1 and f(x | 1 << i)]
    M = len(pairs)
    rows = [x for x, i in pairs] + [x | 1 << i for x, i in pairs]
    raw = [sum(((rows[k] >> v) & 1) << k for k in range(2 * M)) for v in range(8)]
    sites = [next(k for k, (x, i) in enumerate(pairs) if i == v) for v in range(8)]
    if not replay(M, raw):
        sys.exit('the search does not close for this graph: no file written')
    m = re.search(r'def rawInputs : List W :=\s*\[(.*?)\]', src, re.S)
    newraw = 'def rawInputs : List W :=\n  [' + ',\n   '.join(hex(v) for v in raw) + ']'
    src = src[:m.start()] + '@@RAW@@' + src[m.end():]
    assert '0x' not in src
    src = re.sub(r'\b340\b', str(2 * M), src)
    src = re.sub(r'\b170\b', str(M), src)
    src = src.replace('@@RAW@@', newraw)
    old_sites = '[1, 0, 2, 7, 17, 25, 48, 93]'
    assert old_sites in src
    src = src.replace(old_sites, '[' + ', '.join(map(str, sites)) + ']')
    g_old = ('  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||\n'
             '  (x 0 && x 5) || (x 0 && x 6) || (x 2 && x 7)')
    assert g_old in src
    src = src.replace(g_old, '  ' + ' || '.join(f'(x {a} && x {b})' for a, b in E))
    h_old = ('(x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||\n'
             '      (x 4 &&& x 5) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 7) =')
    assert h_old in src
    src = src.replace(h_old, ' ||| '.join(f'(x {a} &&& x {b})' for a, b in E) + ' =')
    i = src.index('theorem PEqualNP.Outside.L_meta_528')
    stmt = open(stmt_file).read().strip()
    src = (src[:i] + f'theorem PEqualNP.Outside.{ident} : ' + stmt +
           ' :=\n  Check528.lower_of_optimized Check528.all_front\n')
    src = (src.replace('Live528', f'PEqualNP.Outside.{ident}.Live')
              .replace('Check528', f'PEqualNP.Outside.{ident}.Check'))
    src = src.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n'
                      '-- Search checker adapted from the accepted proof L-meta-528; the rows are the '
                      'sensitive\n-- pairs of this graph.\n', 1)
    open(out, 'w').write(src)
    print(f'wrote {out}: {M} row pairs, {len(src)} bytes')

def replay(M, raw):
    FULL = (1 << (2 * M)) - 1
    LOW = (1 << M) - 1
    neg = lambda x: x ^ FULL
    canon = lambda x: neg(x) if x & 1 else x
    sep = lambda x: (x ^ (x >> M)) & LOW
    goal = canon(LOW << M)
    inputs = [canon(v) for v in raw]
    def singles(l):
        if not l: return []
        a, rest = l[0], l[1:]
        return [(a, rest)] + [(b, [a] + bs) for b, bs in singles(rest)]
    def pairs(l):
        if not l: return []
        a, rest = l[0], l[1:]
        return [(a, b, bs) for b, bs in singles(rest)] + [(b, c, [a] + bs) for b, c, bs in pairs(rest)]
    def cuts(ws):
        v = 0
        for w in ws: v |= sep(w)
        return v
    count = [0]
    def dispatch(extra, k, a, b, r):
        base = cuts(r)
        for w in (a & b, a & neg(b), neg(a) & b, neg(a) & neg(b)):
            v = sep(w) | base
            if v == LOW and opt(k, extra, [canon(w)] + r): return True
            if extra != 0:
                if (v | sep(a)) == LOW and opt(k, extra - 1, [canon(w), a] + r): return True
                if (v | sep(b)) == LOW and opt(k, extra - 1, [canon(w), b] + r): return True
            if extra >= 2 and (v | sep(a) | sep(b)) == LOW and opt(k, extra - 2, [canon(w), a, b] + r):
                return True
        return False
    def opt(k, extra, ws):
        count[0] += 1
        if count[0] > 3000000: sys.exit('the search is too large to replay')
        if ws == [goal]: return True
        if k == 0: return False
        return any(dispatch(extra, k - 1, a, b, r) for a, b, r in pairs(ws))
    ok = not any(dispatch(2, 8, a, b, r) for a, b, r in pairs(inputs))
    print(f'search replay: {count[0]} positions, closes: {ok}')
    return ok

if __name__ == '__main__':
    main()
