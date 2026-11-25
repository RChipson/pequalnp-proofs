# Exhaustive over graphs with no 4-cycle up to isomorphism (built vertex by vertex, exact
# isomorphism test inside buckets of a cheap invariant), no isolated vertex, cover number 2..5.
import sys, itertools, time
from orc import solve, mis
NMAX=int(sys.argv[1])
def c4free(adj,n):
    for a in range(n):
        for c in range(a+1,n):
            if bin(adj[a]&adj[c]).count('1')>=2: return False
    return True
def inv(adj,n):
    deg=[bin(a).count('1') for a in adj]
    return tuple(sorted((deg[v],tuple(sorted(deg[u] for u in range(n) if adj[v]>>u&1))) for v in range(n)))
def iso(a1,a2,n):
    deg1=[bin(a).count('1') for a in a1]; deg2=[bin(a).count('1') for a in a2]
    order=sorted(range(n),key=lambda v:-deg1[v])
    mp={}; used=[False]*n
    def bt(i):
        if i==n: return True
        v=order[i]
        for w in range(n):
            if used[w] or deg2[w]!=deg1[v]: continue
            ok=True
            for u,x in mp.items():
                if ((a1[v]>>u)&1)!=((a2[w]>>x)&1): ok=False;break
            if ok:
                mp[v]=w; used[w]=True
                if bt(i+1): return True
                del mp[v]; used[w]=False
        return False
    return bt(0)
level={(): [[]]}  # n=0
cur=[[]]
t0=time.time(); total=0; found=0
for n in range(1,NMAX+1):
    buckets={}
    for g in cur:
        for mask in range(1<<(n-1)):
            adj=g[:]+[mask]
            for u in range(n-1):
                if mask>>u&1: adj[u]|=1<<(n-1)
            if not c4free(adj,n): continue
            k=inv(adj,n)
            b=buckets.setdefault(k,[])
            if any(iso(adj,h,n) for h in b): continue
            b.append(adj)
    cur=[g for b in buckets.values() for g in b]
    tested=0
    V=set(range(n))
    for adj in cur:
        if any(a==0 for a in adj): continue
        edges=[(a,b) for a in range(n) for b in range(a+1,n) if adj[a]>>b&1]
        M=mis(n,edges)
        t=n-max(len(m) for m in M)
        if t>5 or t<2: continue
        tested+=1
        ok,res=solve(n,[V-set(m) for m in M],[V-set(e) for e in edges],t-1)
        if ok:
            found+=1
            print('COUNTEREXAMPLE n',n,'edges',edges,'cover',t,'dual circuit',res,flush=True)
    total+=tested
    print('n',n,'classes',len(cur),'tested',tested,'counterexamples so far',found,'secs',round(time.time()-t0,1),flush=True)
