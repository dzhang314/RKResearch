"""Exact split-CRT diagonals for the arithmetic-front literal silent stars."""
from regular_star_projection import raw
from arith_star_diagonal import int_input
from flint import nmod_mpoly_ctx,fmpz_poly
from time import perf_counter
from math import gcd
from functools import lru_cache
from sympy import nextprime,isprime

def mod_images(P,Q,p,z,cap,degs):
    assert z*z%p==2
    X=nmod_mpoly_ctx.get(['g','s'],p)
    W=[]
    for a in (z,p-z):
        inputs=[]
        for U,V in (P,Q):
            inputs.append(X.from_dict({c:(U.get(c,0)+a*V.get(c,0))%p for c in U.keys()|V.keys()}))
        U,V=inputs
        if (U.degrees()[1],V.degrees()[1])!=degs:return None
        R=[0]*(cap+1)
        for (i,j),v in U.resultant(V,1).to_dict().items():
            assert not j and i<=cap
            R[i]=int(v)
        W.append(R)
    Z0=pow(2,-1,p);Z1=pow(2*z,-1,p)
    return ([(x+y)*Z0%p for x,y in zip(*W)],[(x-y)*Z1%p for x,y in zip(*W)])

@lru_cache(None)
def reconstruct(slot):
    P,Q,_,_,_=raw(False,slot)
    s0,g0=P.degrees()[1:3];s1,g1=Q.degrees()[1:3]
    degs=(s0,s1)
    assert (s0,g0,s1,g1)==(10,29,24,79) if slot==4 else (s0,g0,s1,g1)==(9,29,26,79)
    U,V=int_input(P),int_input(Q)
    cap=s0*g1+s1*g0
    bound=U[2]**s1*V[2]**s0
    H=[[0]*(cap+1) for _ in range(2)]
    n=0;modulus=1;p=2**60;begin=perf_counter()
    print('literal exact CRT start',slot,cap,bound.bit_length(),flush=True)
    while modulus<=2*bound:
        p=int(nextprime(p))
        if p%8!=7:continue
        assert isprime(p)
        W=mod_images(U[:2],V[:2],p,pow(2,(p+1)//4,p),cap,degs)
        if W is None:continue
        mi=pow(modulus,-1,p)
        H=[[x+modulus*((a-x)*mi%p) for a,x in zip(A,B)] for A,B in zip(W,H)]
        n+=1;modulus*=p
        if n%12==0:print('literal CRT progress',slot,n,round(perf_counter()-begin,1),flush=True)
    H=[[a if 2*a<modulus else a-modulus for a in v] for v in H]
    assert all(abs(a)<=bound for q in H for a in q)
    p0=1129;W=mod_images(U[:2],V[:2],p0,406,cap,degs)
    assert all((a-b)%p0==0 for Q,R in zip(W,H) for a,b in zip(Q,R))
    R=list(map(fmpz_poly,H));d=max(v.degree() for v in R)
    h=min(next((i for i,a in enumerate(v) if a),cap+1) for v in R)
    if slot==4:assert (d,h,n,bound.bit_length())==(1486,288,89,5312)
    D=gcd(*(int(v.content()) for v in R))
    print('exact quadratic literal resultant',slot,d,'valuation',h,'primes',n,round(perf_counter()-begin,1),flush=True)
    A,B=[(x//D).right_shift(h) if x else x for x in R]
    return A,B

@lru_cache(None)
def norm_factors(slot):
    A,B=reconstruct(slot)
    N=A*A-2*B*B; assert N
    N=N//N.content(); F=[];prod=fmpz_poly([1])
    for S,e in N.factor_squarefree()[1]:
        for M,k in S.factor()[1]:
            assert k==1
            prod*=M**e;F.append((M,e))
    assert prod==N or prod==-N
    if slot==4:assert N.degree()==2396
    print('literal exact rational norm and factors',slot,N.degree(),[(M.degree(),e) for M,e in F],flush=True)
    return F
