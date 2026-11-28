"""Exact rational primitive resultant and its complete characteristic-zero factors."""
from regular_star_projection import raw
from flint import fmpz_mpoly_ctx,fmpz_poly,fmpq_poly
from math import lcm,gcd
from time import perf_counter
def primitive(P,C):
    vals={};L=1
    for (i,j,k,l),a in P.to_dict().items():
        assert i==l==0
        v,w=int(a.p),int(a.q)
        L=lcm(L,w);vals[k,j]=(v,w)
    vals={e:v*(L//w) for e,(v,w) in vals.items()}
    D=gcd(*vals.values())
    return C.from_dict({e:w//D for e,w in vals.items()})

def factor_diagonal():
    C=fmpz_mpoly_ctx.get(['g','s'])
    F,G,*_=raw(True,4)
    P,Q=(primitive(v,C) for v in (F,G))
    assert P.degrees()==(29,10) and Q.degrees()==(79,24)
    result=P.resultant(Q,1)
    vals={}
    for (ig,is0),a in result.to_dict().items():
        assert not is0
        vals[ig]=a
    N=fmpz_poly([vals.get(i,0) for i in range(max(vals,default=-1)+1)])
    assert N.degree()==1486 and all(N[i]==0 for i in range(288)) and N[288]
    N=N.right_shift(288)
    N=N//N.content()
    assert N.degree()==1198
    prod=fmpz_poly([1]);out=[]
    for X,e in N.factor_squarefree()[1]:
        for P,k in X.factor()[1]:
            assert k==1
            prod*=P**e
            M=fmpq_poly(P)
            out.append((M*(1/M[M.degree()]),e))
    assert prod==N or prod==-N
    print('exact degree-1198 diagonal factorization',[(M.degree(),e) for M,e in out],flush=True)
    return out
