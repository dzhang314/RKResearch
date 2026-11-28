"""Quadratic-field CRT proposals, accepted only by exact divisibility."""
from arith_star_fibers import E, Bfield, ExField, trim, sc, modgamma, gcdp, qr, mul, orient
from flint import fmpq_poly as P,fmpq,nmod_poly
from sympy import nextprime
from math import isqrt
from time import perf_counter

def prime_series():
    m=2**60
    while True:
        p=int(nextprime(m));m=p
        if p%8==7:
            t=pow(2,(p+1)//4,p)*pow(2,-1,p)%p
            assert 2*t*t%p==1
            yield p,t

def rat(a,m):
    n=isqrt(m//2)
    q,r=m,a%m;u,v=0,1
    while r>n:
        c,z=divmod(q,r);q,r=r,z;u,v=v,u-c*v
    if not v or abs(v)>n:return None
    z=fmpq(r,v)
    if (a*int(z.q)-int(z.p))%m:return None
    return z

def recover(n,compute,verify,desc):
    M=1;R=[[0]*n for _ in range(2)];count=0;start=perf_counter()
    for p,t in prime_series():
        if count>=80:break
        count+=1
        try:x,y=(compute(p,tl) for tl in (t,p-t))
        except (ArithmeticError,ValueError,ZeroDivisionError):
            continue
        if len(x)!=len(y) or len(x)!=n:continue
        A,B=pow(2,-1,p),pow(2*t,-1,p)
        S=[[(a+b)*A%p for a,b in zip(x,y)],[(a-b)*B%p for a,b in zip(x,y)]]
        m=pow(M,-1,p)
        R=[[a+M*((d-a)*m%p) for a,d in zip(v,k)] for v,k in zip(R,S)]
        M*=p
        q=[[rat(x,M) for x in v] for v in R]
        if any(x is None for v in q for x in v):continue
        ans=verify(*q)
        if ans is not None:
            print('exact paired CRT proposal verified',desc,M.bit_length(),round(perf_counter()-start,2),flush=True)
            return ans
    raise ArithmeticError(f'exact paired CRT proposal failed: {desc}')

def mod_poly(V,p,t):
    K=Bfield(nmod_poly([0,1],p),p,t)
    return K.cast(V)

def fast_orientation(M,n):
    J=orient()
    assert not M.b and n<=M.degree()
    J=E(J.a%M.a,J.b%M.a)
    def trial(p,t):
        A=modgamma(M,p,t)
        U=mod_poly(J,p,t)
        G=A.gcd(U)
        if G.degree()!=n:return []
        return [int(G[i]) for i in range(n)]
    def verify(A,B):
        S=E(P([*A,1]),P(B))
        if M%S or J%S:return None
        Q=M.exact(S)
        # Independently certify the conjugate complement has no actual
        # common orientation root. Q is monic at this residue place.
        p,t=1129,203
        R=modgamma(Q,p,t)
        U=mod_poly(J,p,t)
        if R.gcd(U).degree()!=0:return None
        return S
    F=recover(n,trial,verify,('orientation',M.degree(),n))
    return F

def reduced_support(F,G,K):
    F=trim([K(v.v) for v in F]);G=trim([K(v.v) for v in G])
    if not F or not G:raise ArithmeticError('leading')
    R=[K(1)]
    while len(F)>1:
        D=gcdp(F,G)
        if len(D)<=1:break
        F,r=qr(F,D)
        assert not r and F
        R=mul(R,D)
    return R

def fast_guard(K,F,G,n,tag):
    M=K.M
    n0=M.degree()
    def trial(p,t):
        U=Bfield(modgamma(M,p,t),p,t)
        D=reduced_support(F,G,U)
        if len(D)!=n+1:return []
        return [int(v.x[i]) for v in D[:-1] for i in range(n0)]
    def verify(A,B):
        D=[K(E(P(A[i:i+n0]),P(B[i:i+n0]))) for i in range(0,n*n0,n0)]+[K(1)]
        Q,R=qr(F,D)
        if R or not Q:return None
        Y=[K(1)]
        for _ in range(n):Y=qr(mul(Y,G),D)[1]
        if Y:return None
        return Q
    return recover(n*n0,trial,verify,('guard',tag,M.degree(),n))
