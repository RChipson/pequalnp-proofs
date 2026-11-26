"""A stronger OR sharing than cse.paar for families of small sets: first choose, by simulated annealing,
a matching of elements into pairs inside every set so that as many pairs as possible are used by two or
more sets (each extra use of a pair saves one OR gate); then let cse.paar share what is left.
pre_pairs(sets, seconds, rnd) returns the family rewritten over new items plus the pair definitions."""
import collections, math, random, time
def pre_pairs(sets, seconds, rnd):
    sets = [sorted(s) for s in sets]
    m = len(sets)
    mate = [dict() for _ in range(m)]            # element -> partner inside set i
    cnt = collections.Counter()                  # pair -> number of sets using it
    def gain_add(p): return 1 if cnt[p] >= 1 else 0
    def gain_del(p): return -1 if cnt[p] >= 2 else 0
    cur = 0; best = 0; bestmate = None
    t_end = time.time() + seconds; it = 0; T = 0.6
    big = [i for i in range(m) if len(sets[i]) >= 2]
    if not big: return [set(s) for s in sets], []
    while True:
        it += 1
        if it % 4096 == 0:
            left = t_end - time.time()
            if left <= 0: break
            T = 0.05 + 0.55 * left / seconds
        i = rnd.choice(big); s = sets[i]
        a, b = rnd.sample(s, 2)
        if mate[i].get(a) == b:
            # break the pair
            p = (min(a, b), max(a, b)); d = gain_del(p)
            if d < 0 and rnd.random() >= math.exp(d / T): continue
            cnt[p] -= 1; del mate[i][a]; del mate[i][b]; cur += d
        else:
            d = 0; rem = []
            for x in (a, b):
                y = mate[i].get(x)
                if y is not None:
                    q = (min(x, y), max(x, y)); rem.append((x, y, q))
            # removing (possibly two) pairs, adding one
            for x, y, q in rem: d += gain_del(q)
            p = (min(a, b), max(a, b))
            d += 1 if cnt[p] >= 1 else 0
            if d < 0 and rnd.random() >= math.exp(d / T): continue
            for x, y, q in rem:
                cnt[q] -= 1; del mate[i][x]; del mate[i][y]
            cnt[p] += 1; mate[i][a] = b; mate[i][b] = a; cur += d
        if cur > best: best = cur; bestmate = [dict(x) for x in mate]
    if bestmate is None: return [set(s) for s in sets], []
    use = collections.Counter()
    for i in range(m):
        for a, b in bestmate[i].items():
            if a < b: use[(a, b)] += 1
    nxt = max(max(s) for s in sets if s) + 1
    defs = []; name = {}
    out = []
    for i in range(m):
        s = set(sets[i])
        for a, b in bestmate[i].items():
            if a < b and use[(a, b)] >= 2:
                if (a, b) not in name: name[(a, b)] = nxt; defs.append((nxt, a, b)); nxt += 1
                s.discard(a); s.discard(b); s.add(name[(a, b)])
        out.append(s)
    return out, defs
