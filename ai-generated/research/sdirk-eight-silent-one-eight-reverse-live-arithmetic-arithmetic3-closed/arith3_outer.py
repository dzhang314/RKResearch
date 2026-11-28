"""Bounded exact diagonal/actual terminal-clock projection of the two geometric reads."""
from arith3_projection import swap,projection,rankdrop
from arith2_aux import fn
from arith_star_diagonal import int_input
from arith_star_fibers import gpoly,modgamma
from regular_star_projection import Co,red
from quadratic_poly import E
from flint import fmpq_poly as P,fmpz_poly,nmod_poly
from functools import lru_cache
from math import gcd
from time import perf_counter
from sympy import nextprime
import gzip,sys
sys.set_int_max_str_digits(0)

@lru_cache(None)
def inputs():
    D,R,*_=projection()
    A,B=map(lambda f:int_input(swap(f)),(D,R))
    return A,B

def images(p,t,fast=True):
    A,B=inputs()
    assert 2*t*t%p==1
    return fn(A,B,p,(2*t)%p,9,66,fast)

def pure_ordinary_bound():
    A,B=inputs()
    return A[-1]**66*B[-1]**9

def exact():
    A,B=inputs();CAP=2268;bound=pure_ordinary_bound()
    p=2**60;M=1;W=[[0]*(CAP+1) for _ in range(2)];n=0;ts=perf_counter()
    while M<=2*bound:
        p=int(nextprime(p+1000))
        if p%8!=7:continue
        z=pow(2,(p+1)//4,p);assert z*z%p==2
        tt=z*pow(2,-1,p)%p
        V=images(p,tt)
        if V is None:continue
        assert all(len(L)==CAP+1 for L in V)
        if n==0:assert V==images(p,tt,False)
        y=pow(M,-1,p)
        for U,L in zip(W,V):
            for j,b in enumerate(L):U[j]+=M*((b-U[j])*y%p)
        M*=p;n+=1
        if n%32==0:print('stage3 exact diagonal CRT progress',n,round(perf_counter()-ts,2),flush=True)
    W=[[q if 2*q<M else q-M for q in L] for L in W]
    assert all(abs(q)<=bound for L in W for q in L)
    T=images(65537,2040,False)
    assert T and all((a-b)%65537==0 for U,V in zip(W,T) for a,b in zip(U,V))
    h=min(next((i for i,a in enumerate(L) if a),CAP+1) for L in W)
    d=max(max((i for i,a in enumerate(L) if a),default=-1) for L in W)
    assert (h,d,n,bound.bit_length())==(366,2268,132,7916)
    c=gcd(*(gcd(*U) for U in W))
    print('stage3 exact geometric terminal-clock result',CAP,h,d,d-h,n,bound.bit_length(),round(perf_counter()-ts,2),flush=True)
    with gzip.open('arith3-exact-oriented.gz','wt') as f:
        for U in W:f.write(' '.join(str(a//c) for a in U[h:d+1])+'\n')

def loadQ():
    with gzip.open('arith3-exact-oriented.gz','rt') as f:
        C,D=(P(list(map(int,next(f).split()))) for _ in range(2))
    return E(C,2*D)

@lru_cache(None)
def gguards():
    return [gpoly(G) for G in projection()[-1][:5]]

def checked_quotient(A,G):
    """Exact division in Q(t)[gamma] via one rational conjugate norm."""
    T=E(G.a,-G.b);N=G*T
    assert N.a and not N.b
    B=A*T
    q,r=divmod(B.a,N.a);v,w=divmod(B.b,N.a)
    if r or w:return None
    return E(q,v)

def strip(A,guards=None):
    if guards is None:guards=gguards()
    result=[]
    for G in guards:
        e=0
        while True:
            Q=checked_quotient(A,G)
            if Q is None:break
            A=Q;e+=1
            assert A
        result.append(e)
    return A,result

if __name__=='__main__':exact()
