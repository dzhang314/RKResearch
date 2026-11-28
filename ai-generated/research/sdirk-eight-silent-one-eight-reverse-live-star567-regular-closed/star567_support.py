"""Propose fast common support using CRT; accept only an exact audited divisor."""
from math import isqrt
from sympy import nextprime
from flint import fmpq, fmpq_poly
from star567_fibers import Bfield, gcdp, modQ, mul, qr, trim

def rational_recover(a,m):
    bound=isqrt(m//2)
    q,r=m,a%m
    v,w=0,1
    while r>bound:
        d,u=divmod(q,r)
        q,r=r,u
        v,w=w,v-d*w
    if not w or abs(w)>bound:
        return None
    z=fmpq(r,w)
    if (a*int(z.q)-int(z.p))%m:
        return None
    return z

def reduced_support(F,G,K):
    F=trim([K(modQ(v.x,K.p)) for v in F])
    G=trim([K(modQ(v.x,K.p)) for v in G])
    if not F or not G:
        raise ArithmeticError("reduced proposal not finite")
    Z=[K(1)]
    while len(F)>1:
        D=gcdp(F,G)
        if len(D)<=1:
            break
        F,r=qr(F,D)
        assert not r and F
        Z=mul(Z,D)
    return Z

def exact_support_division(F,G,n,K):
    # The modular path is only a proposal. The two exact divisions at
    # return are all that is needed to license exclusion of its support.
    M=K.M
    degree=M.degree()
    coefficients=[0]*(n*degree)
    p=2**60
    modulus=1
    for _ in range(80):
        p=int(nextprime(p+1000))
        try:
            Mm=modQ(M,p)
            if Mm.degree()!=degree or Mm.leading_coefficient()!=1:
                continue
            B=Bfield(Mm,p,0)
            Z=reduced_support(F,G,B)
        except (ArithmeticError,ValueError,ZeroDivisionError):
            continue
        if len(Z)!=n+1:
            continue
        inverse=pow(modulus,-1,p)
        vv=[int(c.x[i]) for c in Z[:-1] for i in range(degree)]
        for j,a in enumerate(vv):
            coefficients[j]+=modulus*((a-coefficients[j])*inverse % p)
        modulus*=p
        rr=[rational_recover(a,modulus) for a in coefficients]
        if any(a is None for a in rr):
            continue
        D=[K(fmpq_poly(rr[i:i+degree])) for i in range(0,len(rr),degree)]+[K(1)]
        Q,R=qr(F,D)
        if R or not Q:
            continue
        GN=[K(1)]
        for _ in range(n):
            GN=qr(mul(GN,G),D)[1]
        if GN:
            continue
        assert len(D)==n+1 and D[-1]==1 and len(Q)==len(F)-n
        return Q
    raise ArithmeticError("no supported exact divisor was recovered")
