import json,sys
R=json.load(open(sys.argv[1])); n=int(sys.argv[2]); C=json.load(open(sys.argv[3]))
h=lambda x:'%016x %016x'%(x>>64,x&((1<<64)-1))
open(sys.argv[4],'w').write('\n'.join(h(r) for r in R)+'\n')
cols=[sum(((R[u]>>v)&1)<<u for u in range(n)) for v in range(n)]
mask=lambda l:sum(1<<i for i in l)
L=[(mask(S),mask(T)) for S,T,c in C]+[(1<<u,R[u]) for u in range(n)]+[(cols[v],1<<v) for v in range(n)]
open(sys.argv[5],'w').write(str(len(L))+'\n'+'\n'.join(h(S)+' '+h(T) for S,T in L)+'\n')
