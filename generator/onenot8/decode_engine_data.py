import re,sys
src=open(sys.argv[1]).read()
def big(k):
    m=re.search(r'^def bigNat_%d : Nat := (.*)$'%k, src, re.M); e=m.group(1)
    # nested Nat.lor (Nat.shiftLeft (X) 64) 0x...
    words=re.findall(r'0x[0-9a-f]+', e)   # most significant first
    v=0
    for w in words: v=(v<<64)|int(w,16)
    return v
NN=int(re.search(r'def NN : Nat := (\d+)',src).group(1))
AA,HX,HY=big(0),big(1),big(2); raw=[big(3+i) for i in range(8)]; TG=big(11)
segsX=eval(re.search(r'def segsX : List \(ℕ × ℕ\) := (\[.*\])',src).group(1)); segsY=eval(re.search(r'def segsY : List \(ℕ × ℕ\) := (\[.*\])',src).group(1))
f_edges=re.findall(r'\(x (\d) && x (\d)\)', re.search(r'def f \(x : Fin 8 → Bool\) : Bool := (.*)',src).group(1)); E=[(int(a),int(b)) for a,b in f_edges]
def fv(x): return any(x>>a&1 and x>>b&1 for a,b in E)
print('NN',NN,'edges',E,'len raw bits',[r.bit_length() for r in raw][:3])
def X(i): return sum(((raw[v]>>i)&1)<<v for v in range(8))
def Y(i): return sum(((raw[v]>>(NN+i))&1)<<v for v in range(8))
b=lambda x:format(x,'08b')[::-1]
print('rows 0..70:')
for i in range(0,76): print(i,b(X(i)),b(Y(i)),'f(x)',int(fv(X(i))),'f(y)',int(fv(Y(i))),'AA',AA>>i&1,'TG',TG>>i&1,'HX',HX>>i&1,'HY',HY>>i&1)
print('segsX',len(segsX),segsX[:6],'...',segsX[-3:]); print('segsY',len(segsY),segsY[:4],'...',segsY[-3:])
import collections
print('popcount AA',bin(AA).count('1'),'TG',bin(TG).count('1'))
# check hypothesis: in X segment rows share x; in Y share y
okx=all(len({X(i) for i in range(s+1,e)})==1 for s,e in segsX); oky=all(len({Y(i) for i in range(s+1,e)})==1 for s,e in segsY)
print('X segments share x:',okx,'Y segments share y:',oky)
for s,e in segsX[:4]: print('X seg',s,e,[ (b(X(i)),b(Y(i))) for i in range(s,e+1)])
for s,e in segsY[:3]: print('Y seg',s,e,[ (b(X(i)),b(Y(i))) for i in range(s,e+1)])
print('=========== analysis')
allv=range(256)
indep=[s for s in allv if not fv(s)]
def maximal(s): return all(fv(s|(1<<v)) for v in range(8) if not s>>v&1)
MIS=[s for s in indep if maximal(s)]
print('independent sets',len(indep),'maximal',len(MIS),[b(s) for s in MIS])
pc=lambda s:bin(s).count('1')
xs=[X(s+1) for s,e in segsX]; ys=[Y(s+1) for s,e in segsY]
print('distinct x',len(set(xs)),'by size',collections.Counter(pc(x) for x in xs)); print('distinct y',len(set(ys)),'by size',collections.Counter(pc(y) for y in ys))
print('y list:',[b(y) for y in ys])
print('y that are MIS:',sum(1 for y in ys if y in MIS),'of',len(MIS))
pairsX=set((X(i),Y(i)) for s,e in segsX for i in range(s+1,e)); pairsY=set((X(i),Y(i)) for s,e in segsY for i in range(s+1,e))
print('pairs',len(pairsX),len(pairsY),'equal sets',pairsX==pairsY)
cls=collections.Counter()
for x,y in pairsX:
    k=('edge' if pc(x)==2 else 'x%d'%pc(x), 'empty' if y==0 else 'single' if pc(y)==1 else 'MIS' if y in MIS else 'sub1' if (y&~x)==0 and pc(x^y)==1 else 'other', 'ysubx' if (y&~x)==0 else 'ynotsub', 'dist%d'%pc(x^y))
    cls[k]+=1
for k,v in sorted(cls.items()): print(v,k)
# are all (edge, MIS) pairs present? all (edge, empty)? (edge, singleton in edge)?
edges=[(1<<a)|(1<<c) for a,c in E]
print('edge x MIS present:',sum(1 for x in edges for y in MIS if (x,y) in pairsX),'of',len(edges)*len(MIS))
print('x of size 3:',[b(x) for x in xs if pc(x)==3][:30])
tr3=[s for s in allv if pc(s)==3 and fv(s)]; print('true points of size 3:',len(tr3),'present as x:',sum(1 for s in tr3 if s in xs))
tr4=[s for s in allv if pc(s)==4 and fv(s)]; print('true points of size 4:',len(tr4),'present as x:',sum(1 for s in tr4 if s in xs))
# sub1 pairs: for x true and v in x with x-v false: present?
cnt=0;tot=0
for x in allv:
    if fv(x):
        for v in range(8):
            if x>>v&1 and not fv(x^(1<<v)):
                tot+=1; cnt+=((x,x^(1<<v)) in pairsX)
print('all boundary pairs (x true, x-v false):',tot,'present',cnt)
fp=[X(i) for i in range(64)]; print('first 64 rows: distinct',len(set(fp)),'sizes',collections.Counter(pc(x) for x in fp),'all true',all(fv(x) for x in fp),'in xs',sum(1 for x in fp if x in xs))
truepts=[s for s in allv if fv(s)]; print('true points',len(truepts),'not in xs',len([s for s in truepts if s not in xs]))
print('fp sorted as ints',sorted(fp)[:20]); print('fp in order',fp[:20])
