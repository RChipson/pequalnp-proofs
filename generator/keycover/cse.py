import sys,collections,random
def paar(sets,rnd=None):
    """sets: list of frozensets of base items (ints). Returns (gates, defs, exprs):
    defs: list of (new_item, a, b); exprs: per set the list of items whose union is the set."""
    cur=[set(s) for s in sets]
    nxt=max((max(s) for s in sets if s),default=0)+1
    defs=[]
    # merge identical sets later (they share all gates): handle by dedup
    while True:
        cnt=collections.Counter()
        for s in cur:
            l=sorted(s)
            for i in range(len(l)):
                for j in range(i+1,len(l)): cnt[(l[i],l[j])]+=1
        if not cnt: break
        mx=max(cnt.values())
        if mx<2: break
        top=[p for p,c in cnt.items() if c==mx]
        a,b=(rnd.choice(top) if rnd else top[0])
        z=nxt; nxt+=1; defs.append((z,a,b))
        for s in cur:
            if a in s and b in s: s.discard(a); s.discard(b); s.add(z)
    # identical remaining sets (as item sets) share their final unions
    seen={}; gates=len(defs)
    for s in cur:
        k=frozenset(s)
        if k in seen: continue
        seen[k]=1; gates+=max(0,len(s)-1)
    return gates,defs,cur
if __name__=='__main__':
    pc=lambda x:bin(x).count('1')
    B=[]
    for l in open(sys.argv[1]):
        p=l.split(); B.append((int(p[1]+p[2],16),int(p[3]+p[4],16)))
    bits=lambda x:frozenset(i for i in range(128) if x>>i&1)
    gx,_,_=paar([bits(S) for S,T in B]); gy,_,_=paar([bits(T) for S,T in B])
    m=len(B); W=sum(pc(S)+pc(T) for S,T in B)
    print('blocks',m,'weight',W,'no sharing',W-1,'with sharing',gx+gy+2*m-1,'(row side',gx,'col side',gy,')')
