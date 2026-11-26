import json,sys,collections
# usage: plant2.py table.json n out.json -- closed all-ones blocks by greedy growth from every pair of rows and of columns
R=json.load(open(sys.argv[1])); n=int(sys.argv[2])
pc=lambda x:bin(x).count('1')
FULL=(1<<n)-1
cols=[sum(((R[u]>>v)&1)<<u for u in range(n)) for v in range(n)]
def bits(x): return [i for i in range(n) if x>>i&1]
def grow_all(Rw,Cw,found,flip):
    # Rw: row masks over columns; Cw: column masks over rows
    def closeT(T):
        S=FULL
        x=T
        while x:
            l=x&-x; S&=Cw[l.bit_length()-1]; x^=l
        return S
    def closeS(S):
        T=FULL
        x=S
        while x:
            l=x&-x; T&=Rw[l.bit_length()-1]; x^=l
        return T
    for a in range(n):
        for b in range(a):
            T=Rw[a]&Rw[b]
            if pc(T)<2: continue
            S=(1<<a)|(1<<b)
            while True:
                Sc=closeT(T); Tc=closeS(Sc)
                s=pc(Sc); t=pc(Tc)
                if s*t>=2.0*(s+t):
                    key=(Sc,Tc) if not flip else (Tc,Sc)
                    found[key]=found.get(key,0)+1
                S=Sc
                best=0;bw=-1
                for w in range(n):
                    if S>>w&1: continue
                    c=pc(T&Rw[w])
                    if c>best: best=c;bw=w
                if best<2: break
                T&=Rw[bw]; S|=1<<bw
found={}
grow_all(R,cols,found,False)
grow_all(cols,R,found,True)
res=[(pc(S)*pc(T)/(pc(S)+pc(T)),pc(S),pc(T),c,S,T) for (S,T),c in found.items()]
res.sort(reverse=True)
print('candidates',len(res))
print(collections.Counter((r[1],r[2]) for r in res).most_common(12))
json.dump([[bits(S),bits(T),c] for _,_,_,c,S,T in res],open(sys.argv[3],'w'))
