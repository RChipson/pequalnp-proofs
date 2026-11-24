"""Decide whether the edge function of a graph has a monotone circuit (AND/OR gates, two
distinct inputs each) with at most K gates, using the frontier search of search1672.py
with no tags.  Signatures are taken on pairs (edge, maximal independent set), which is
enough for monotone circuits.  Usage: python3 search_graph.py <K> <n> <edges a-b,...>
"""
import sys, time, itertools
sys.path.insert(0, 'generator')
import search1672 as S

def setup(n, E):
    adj = {v: set() for v in range(n)}
    for a, b in E: adj[a].add(b); adj[b].add(a)
    def indep(X): return all(not (adj[v] & X) for v in X)
    mis = []
    for m in range(1 << n):
        X = {v for v in range(n) if m >> v & 1}
        if indep(X) and all((adj[v] & X) for v in range(n) if v not in X): mis.append(X)
    pairs = [(set(e), I) for e in E for I in mis]
    bits = len(pairs)
    S.BITS = bits; S.TOP = (1 << bits) - 1; S.TARGET = (S.TOP, 0)
    raw = []
    for v in range(n):
        p = sum(1 << i for i, (e, I) in enumerate(pairs) if v in e)
        q = sum(1 << i for i, (e, I) in enumerate(pairs) if v in I)
        raw.append((p, q, S.NONE))
    return raw, bits, len(mis)

if __name__ == '__main__':
    K = int(sys.argv[1]); n = int(sys.argv[2])
    E = [tuple(map(int, e.split('-'))) for e in sys.argv[3].split(',')]
    raw, bits, nm = setup(n, E)
    print(f'K={K} n={n} edges={len(E)} maximal independent sets={nm} pairs={bits}', flush=True)
    s = S.Searcher(); t0 = time.time()
    r = s.step(K - 1, 0, tuple(raw))
    per = {}
    for key in s.memo: per[key[0]] = per.get(key[0], 0) + 1
    print(f'reachable={r} states={len(s.memo)} replay={1 + s.acc[0]} time={time.time()-t0:.1f}s levels={sorted(per.items(), reverse=True)}', flush=True)
