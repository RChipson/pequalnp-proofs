# Exact search: is there an AND/OR circuit (each gate reads two earlier wires) with k gates that
# represents the n-by-m bipartite graph with the given mask (right at every input with exactly
# one vertex on each side)?
import sys, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc
def build(M, n, m, k, symbreak=True):
    A=lambda u,v:(M>>(m*u+v))&1
    rows=[(u,v) for u in range(n) for v in range(m)]
    NI=n+m
    vid=[0]
    def new():
        vid[0]+=1; return vid[0]
    cls=[]
    selA=[[new() for j in range(NI+i)] for i in range(k)]
    selB=[[new() for j in range(NI+i)] for i in range(k)]
    isand=[new() for i in range(k)]
    val=[[new() for r in rows] for i in range(k)]
    def exactly1(xs):
        cls.append(xs[:])
        for a in range(len(xs)):
            for b in range(a+1,len(xs)): cls.append([-xs[a],-xs[b]])
    for i in range(k):
        exactly1(selA[i]); exactly1(selB[i])
        if symbreak:
            # first operand index < second operand index
            for a in range(NI+i):
                for b in range(a+1):
                    cls.append([-selA[i][a],-selB[i][b]])
        for ri,(u,v) in enumerate(rows):
            def wv(j):
                if j<n: return j==u
                if j<NI: return (j-n)==v
                return val[j-NI][ri]
            a_=new(); b_=new()   # operand values at this row
            for j in range(NI+i):
                x=wv(j)
                for s,o in ((selA[i][j],a_),(selB[i][j],b_)):
                    if x is True: cls.append([-s,o])
                    elif x is False: cls.append([-s,-o])
                    else: cls.append([-s,-x,o]); cls.append([-s,x,-o])
            g=val[i][ri]; t=isand[i]
            # g = t ? a&b : a|b
            cls+= [[-t,-g,a_],[-t,-g,b_],[-t,g,-a_,-b_],[t,g,-a_],[t,g,-b_],[t,-g,a_,b_]]
    # output is the last gate
    for ri,(u,v) in enumerate(rows):
        cls.append([val[k-1][ri]] if A(u,v) else [-val[k-1][ri]])
    # every gate except the last is read by a later gate
    if symbreak:
        for i in range(k-1):
            cls.append([selA[j][NI+i] for j in range(i+1,k)]+[selB[j][NI+i] for j in range(i+1,k)])
    return cls,(selA,selB,isand,NI)
def solve(M,n,m,k):
    cls,(selA,selB,isand,NI)=build(M,n,m,k)
    s=Cadical153(bootstrap_with=cls)
    ok=s.solve()
    res=None
    if ok:
        md=set(x for x in s.get_model() if x>0)
        res=[('AND' if isand[i] in md else 'OR', next(j for j in range(NI+i) if selA[i][j] in md), next(j for j in range(NI+i) if selB[i][j] in md)) for i in range(k)]
    s.delete(); return ok,res
if __name__=='__main__':
    M=int(sys.argv[1]); 
    for k in map(int,sys.argv[2:]):
        t0=time.time(); ok,res=solve(M,4,4,k)
        print('mask',M,'gates',k,'exists' if ok else 'none',round(time.time()-t0,1),res,flush=True)
