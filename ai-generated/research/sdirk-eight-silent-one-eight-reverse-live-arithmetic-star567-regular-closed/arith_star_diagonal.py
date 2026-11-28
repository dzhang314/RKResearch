"""Exact bounded quadratic-integer CRT and exhaustive rational diagonal factors."""
from arith_star_model import two_remainders
from flint import nmod_mpoly_ctx,fmpz_poly
from time import perf_counter
from math import lcm,gcd
from functools import lru_cache
from sympy import nextprime,isprime

def int_input(F):
    dd={};den=1
    for (u,s,g,t),q in F.to_dict().items():
        assert not u and t<=1
        w=q/(2**t)  # z=2t, z^2=2.
        d0,n0=int(w.q),int(w.p)
        den=lcm(den,d0);dd[g,s,t]=(n0,d0)
    rr={K:n*(den//d) for K,(n,d) in dd.items()}
    D=gcd(*rr.values())
    A={};B={}
    for (g,s,t),a in rr.items():
        (B if t else A)[g,s]=a//D
    n=sum(abs(a) for a in A.values())+2*sum(abs(a) for a in B.values())
    return A,B,n

def mod_images(P,Q,p,z,cap):
    assert z*z%p==2
    X=nmod_mpoly_ctx.get(['g','s'],p)
    W=[]
    for a in (z,p-z):
        inputs=[]
        for U,V in (P,Q):
            inputs.append(X.from_dict({c:(U.get(c,0)+a*V.get(c,0))%p for c in U.keys()|V.keys()}))
        U,V=inputs
        if (U.degrees()[1],V.degrees()[1])!=(8,14):return None
        R=[0]*(cap+1)
        for (i,j),v in U.resultant(V,1).to_dict().items():
            assert not j and i<=cap
            R[i]=int(v)
        W.append(R)
    Z0=pow(2,-1,p);Z1=pow(2*z,-1,p)
    return ([(x+y)*Z0%p for x,y in zip(*W)],[(x-y)*Z1%p for x,y in zip(*W)])

@lru_cache(None)
def reconstruct():
    P,Q=two_remainders()
    assert (P.degrees()[1:3],Q.degrees()[1:3])==((8,21),(14,42))
    U,V=int_input(P),int_input(Q)
    cap=8*42+14*21
    bound=U[2]**14*V[2]**8
    H=[[0]*(cap+1) for _ in range(2)]
    n=0;modulus=1;p=2**60;begin=perf_counter()
    print('bounded integer resultant cap/bits',cap,bound.bit_length(),flush=True)
    while modulus<=2*bound:
        p=int(nextprime(p))
        if p%8!=7:continue
        assert isprime(p)
        W=mod_images(U[:2],V[:2],p,pow(2,(p+1)//4,p),cap)
        if W is None:continue
        mi=pow(modulus,-1,p)
        H=[[x+modulus*((a-x)*mi%p) for a,x in zip(A,B)] for A,B in zip(W,H)]
        n+=1;modulus*=p
    H=[[a if 2*a<modulus else a-modulus for a in v] for v in H]
    assert all(abs(a)<=bound for q in H for a in q)
    p0=1129;W=mod_images(U[:2],V[:2],p0,406,cap)
    assert all((a-b)%p0==0 for Q,R in zip(W,H) for a,b in zip(Q,R))
    R=list(map(fmpz_poly,H));d=max(v.degree() for v in R)
    h=min(next((i for i,a in enumerate(v) if a),cap+1) for v in R)
    assert (d,h,n,bound.bit_length())==(630,92,40,2392)
    D=gcd(*(int(v.content()) for v in R))
    print('exact quadratic resultant',d,'valuation',h,'primes',n,round(perf_counter()-begin,1),flush=True)
    A,B=[(x//D).right_shift(h) if x else x for x in R]
    return A,B

@lru_cache(None)
def norm_factors():
    A,B=reconstruct()
    N=A*A-2*B*B; assert N
    N=N//N.content(); F=[];prod=fmpz_poly([1])
    for S,e in N.factor_squarefree()[1]:
        for M,k in S.factor()[1]:
            assert k==1
            prod*=M**e;F.append((M,e))
    assert (prod==N or prod==-N) and N.degree()==1076
    print('exact rational norm and factors',N.degree(),[(M.degree(),e) for M,e in F],flush=True)
    return F
