"""Exact outer determinant of the arithmetic-front silent-eighth chart."""
from arith_silent8_crt import model
from arith_star_diagonal import int_input
from fast_outer_interpolate import get_compiler,fast_mod_images
from flint import nmod_mpoly_ctx,fmpz_poly
from functools import lru_cache
from time import perf_counter
from math import gcd
from sympy import nextprime,isprime

def images(U,V,p,z,cap,d):
    K=nmod_mpoly_ctx.get(['g','s'],p)
    ans=[]
    for sg in (z,p-z):
        P,Q=[K.from_dict({i:(A.get(i,0)+sg*B.get(i,0))%p for i in A.keys()|B.keys()})
             for A,B in (U,V)]
        if tuple(r.degrees()[1] for r in (P,Q))!=d:return None
        R=[0]*(cap+1)
        for (j,i),v in P.resultant(Q,1).to_dict().items():
            assert not i and j<=cap
            R[j]=int(v)
        ans.append(R)
    q=pow(2,-1,p);r=pow(2*z,-1,p)
    return [[(x+y)*q%p for x,y in zip(*ans)],[(x-y)*r%p for x,y in zip(*ans)]]

@lru_cache(None)
def exact_diagonal():
    F,N,*_=model()
    s0,g0=F.degrees()[1:3];s1,g1=N.degrees()[1:3]
    assert (s0,g0,s1,g1)==(32,90,32,69)
    cap=s0*g1+s1*g0
    A,B=int_input(F),int_input(N)
    bound=A[2]**s1*B[2]**s0
    C=[[0]*(cap+1) for _ in range(2)]
    p=2**60;M=1;n=0;vv=perf_counter()
    assert cap==5088 and bound.bit_length()==19691
    use_native=get_compiler() is not None
    print('outer exact bound',cap,bound.bit_length(),'native interpolation',use_native,flush=True)
    while M<=2*bound:
        p=int(nextprime(p))
        if p%8!=7:continue
        assert isprime(p)
        w=pow(2,(p+1)//4,p)
        if use_native:
            rr=fast_mod_images(A[:2],B[:2],p,w,(g0,s0,g1,s1))
            if rr is None:continue
            if n==0:
                assert rr==images(A[:2],B[:2],p,w,cap,(s0,s1))
                print('entire first large-prime image independently checked',p,flush=True)
        else:
            rr=images(A[:2],B[:2],p,w,cap,(s0,s1))
            if rr is None:continue
        mi=pow(M,-1,p)
        C=[[v+M*((x-v)*mi%p) for v,x in zip(vv,ww)] for vv,ww in zip(C,rr)]
        M*=p;n+=1
        if n%32==0:print('outer exact progress',n,M.bit_length(),round(perf_counter()-vv,2),flush=True)
    C=[[v if 2*v<M else v-M for v in vv] for vv in C]
    assert all(abs(v)<=bound for vv in C for v in vv)
    rr=images(A[:2],B[:2],1129,406,cap,(s0,s1))
    assert all((v-w)%1129==0 for vv,ww in zip(C,rr) for v,w in zip(vv,ww))
    Z=list(map(fmpz_poly,C))
    h=min(next((i for i,v in enumerate(z) if v),cap+1) for z in Z)
    dd=max(z.degree() for z in Z)
    assert (dd,h,n)==(5088,464,329)
    c=gcd(*(int(z.content()) for z in Z))
    AA,BB=[(z//c).right_shift(h) if z else z for z in Z]
    print('outer exact diagonal',dd,h,n,round(perf_counter()-vv,2),flush=True)
    return AA,BB
