"""Bounded exact split CRT, using the checked optional geometric resultant kernel."""
from time import perf_counter
from sympy import nextprime,sqrt_mod
from flint import nmod_mpoly_ctx
from small_crt import int_input,image,small_resultant
from geometric_outer import compiler,img
from regular_star_projection import C

def geo_image(F,G,p,z,cap,d):
    """Return split recombination in basis 1,sqrt(2), at the nominal padded degrees."""
    K=nmod_mpoly_ctx.get(['g','y'],p)
    out=[]
    D=cap[0]
    for sgn in (z,p-z):
        assert all(k[1]==0 for pair in (F,G) for P in pair for k in P)
        A,B=[K.from_dict({(i[0],i[2]):(U.get(i,0)+sgn*V.get(i,0))%p
                           for i in U.keys()|V.keys()})
             for U,V in (F,G)]
        if tuple(q.degrees()[1] for q in (A,B))!=d:return None
        R=img(A,B,p)
        if R is None: return None
        assert len(R)<=D+1
        out.append(R+[0]*(D+1-len(R)))
    q=pow(2,-1,p);r=pow(2*z,-1,p)
    return [[(a+b)*q%p for a,b in zip(*out)],[(a-b)*r%p for a,b in zip(*out)]]

def exact_outer(P,Q):
    """Same primitive scales and integer height certificate as small_resultant."""
    s,t=P.degrees()[0],Q.degrees()[0]
    assert s and t and P.degrees()[1]==Q.degrees()[1]==0
    if compiler() is None:return small_resultant(P,Q)
    m=s*Q.degrees()[2]+t*P.degrees()[2]
    cap=(m,0);d=(s,t);A,B=int_input(P),int_input(Q)
    bound=A[2]**t*B[2]**s
    cs=[[0]*(m+1) for _ in range(2)]
    M=1;p=2**60;n=0;start=perf_counter()
    a,b=A[:2],B[:2]
    while M<=2*bound:
        p=int(nextprime(p))
        if p%8!=7:continue
        z=pow(2,(p+1)//4,p);assert z*z%p==2
        R=geo_image(a,b,p,z,cap,d)
        if R is None:R=image(a,b,p,z,cap,d)
        if R is None:continue
        if n==0:
            assert R==image(a,b,p,z,cap,d)
        inv=pow(M,-1,p)
        cs=[[v+M*((x-v)*inv%p) for v,x in zip(Pi,Ri)] for Pi,Ri in zip(cs,R)]
        M*=p;n+=1
        if n%24==0:print('fast split outer exact checkpoint',n,round(perf_counter()-start,2),flush=True)
    assert M>2*bound
    cs=[[v if 2*v<M else v-M for v in A0] for A0 in cs]
    assert all(abs(v)<=bound for A0 in cs for v in A0)
    p=65537;z=int(sqrt_mod(2,p));assert z*z%p==2
    R=image(a,b,p,z,cap,d)
    assert R and all((v-x)%p==0 for T,S in zip(cs,R) for v,x in zip(T,S))
    print('fast split outer exact',s,t,m,n,bound.bit_length(),round(perf_counter()-start,2),flush=True)
    return C.from_dict({(0,0,j,tt):v*2**tt for tt,T in enumerate(cs) for j,v in enumerate(T) if v})

def strip_univariate_guards(P,guards):
    """Strip the known origin power by a coefficient shift, then bounded-degree exact divisions."""
    from aq_gamma import gpoly
    from unequal_finite import E
    from regular_star_projection import remove
    ds=P.to_dict()
    assert ds and all(i==j==0 for (i,j,k,t) in ds)
    v=min(k for (i,j,k,t) in ds)
    assert gpoly(guards[0])==E([0,1])
    shifted=C.from_dict({(0,0,k-v,t):w for (i,j,k,t),w in ds.items()})
    Q,powers=remove(shifted,guards[1:])
    return gpoly(Q),[v]+powers
