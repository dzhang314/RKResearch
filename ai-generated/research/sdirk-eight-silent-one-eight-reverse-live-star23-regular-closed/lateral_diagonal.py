"""Degree-safe exact Q(sqrt(2)) Sylvester reconstruction by bounded integer CRT."""
from regular_star_projection import raw,profile,red,C,con
from flint import nmod_mpoly_ctx,fmpz_poly,fmpz
from time import perf_counter
from quadratic_poly import E
from flint import fmpq_poly
from math import lcm,gcd
from sympy import nextprime,isprime

def int_input(F):
    dd={};den=1
    for (u,s,g,t),q in F.to_dict().items():
        assert not u and t<=1
        # z=2t, z^2=2. Replace every t by z/2 before integer clearing.
        w=q/(2**t)
        d0,n0=int(w.q),int(w.p)
        den=lcm(den,d0);dd[g,s,t]=(n0,d0)
    rr={K:n*(den//d) for K,(n,d) in dd.items()}
    D=gcd(*rr.values())
    A={};B={}
    for (g,s,t),a in rr.items():
        (B if t else A)[g,s]=a//D
    n=sum(abs(a) for a in A.values())+2*sum(abs(a) for a in B.values())
    return A,B,n

def prime_series():
    a=2**60
    while True:
        a=int(nextprime(a))
        if a%8==7 and isprime(a):yield a

def mod_compute(X,Y,p,cap):
    ctx=nmod_mpoly_ctx.get(['g','s'],p)
    z=pow(2,(p+1)//4,p);assert z*z%p==2
    Z=[]
    for a in (z,p-z):
        out=[]
        for A,B in (X,Y):
            ff={k:(A.get(k,0)+a*B.get(k,0))%p for k in A.keys()|B.keys()}
            out.append(ctx.from_dict(ff))
        P,Q=out
        if (P.degrees()[1],Q.degrees()[1])!=(9,26):return None
        V=P.resultant(Q,1);r=[0]*(cap+1)
        for (g,s),v in V.to_dict().items():
            assert not s and g<=cap
            r[g]=int(v)
        Z.append(r)
    uu=pow(2,-1,p);vv=pow(2*z,-1,p)
    return ([(x+y)*uu%p for x,y in zip(*Z)],[(x-y)*vv%p for x,y in zip(*Z)])

def reconstruct(slot=2):
    P,Q,*_=raw(True,slot)
    X,Y=[int_input(P0) for P0 in (P,Q)]
    assert P.degrees()[1:3]==(9,29) and Q.degrees()[1:3]==(26,79)
    cap=9*79+26*29
    bound=X[2]**26*Y[2]**9
    print('fixed resultant integer coefficient bound bits',bound.bit_length(),'vectors',[(len(a),len(b)) for a,b,n in (X,Y)],flush=True)
    primes=prime_series();M=1;n=0;coeffs=[[0]*(cap+1) for _ in range(2)]
    now=perf_counter()
    for p in primes:
        r=mod_compute(X[:2],Y[:2],p,cap)
        if r is None:continue
        c=pow(M,-1,p)
        for i in range(2):
            coeffs[i]=[v+M*(((a-v)%p)*c%p) for a,v in zip(r[i],coeffs[i])]
        M*=p;n+=1
        if n%10==0:print('CRT state',n,M.bit_length(),round(perf_counter()-now,2),flush=True)
        if M>2*bound:break
    coeffs=[[a if 2*a<M else a-M for a in v] for v in coeffs]
    assert all(abs(a)<=bound for j in coeffs for a in j)
    independent=mod_compute(X[:2],Y[:2],1559,cap)
    assert independent is not None
    assert all([x%1559 for x in c0]==c1 for c0,c1 in zip(coeffs,independent))
    uv=[fmpz_poly(a) for a in coeffs]
    assert uv[0] or uv[1]
    raw_deg=max(w.degree() for w in uv)
    o=min(next((i for i,v in enumerate(a) if v),cap+1) for a in uv)
    scal=gcd(*[int(x.content()) for x in uv])
    uv=[(a//scal).right_shift(o) if a else a for a in uv]
    print('exact reconstructed resultant',n,raw_deg,'g valuation',o,'remaining deg',max(w.degree() for w in uv),round(perf_counter()-now,2),flush=True)
    assert (n,raw_deg,o)==(70,1465,265) and max(w.degree() for w in uv)==1200
    return uv


def exact_factors():
    U,V=reconstruct()
    N=U*U-2*V*V
    assert N.degree()==2400
    N=N//N.content()
    D=fmpz_poly([1]);out=[]
    for M,e in N.factor_squarefree()[1]:
        for F,k in M.factor()[1]:
            assert k==1
            D*=F**e
            out.append((E(fmpq_poly(F)).monic(),e))
    assert D==N or D==-N
    print('exact checked norm factors',[(F.degree(),e) for F,e in out],flush=True)
    return E(fmpq_poly(U),2*fmpq_poly(V)),out
