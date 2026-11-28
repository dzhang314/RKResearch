"""Checkpointed serial exact Q(sqrt(2)) arithmetic-front/rear nonliteral six/seven diagonals."""
from arith67_model import model
from arith_star_diagonal import int_input
from geometric_outer import compiler,img
from rear67_exact import full_native
from flint import fmpz_mpoly_ctx
from sympy import nextprime
from time import perf_counter
from functools import lru_cache
from math import gcd
import gzip
import sys
sys.set_int_max_str_digits(0)

I=fmpz_mpoly_ctx.get(['g','s'])
@lru_cache(None)
def ab():
    M=model();F=(M[0],M[2])
    return tuple(int_input(X) for X in F)
def residue_inputs(p,z):
    assert z*z%p==2
    U=[]
    for A,B,_ in ab():
        U.append(I.from_dict({j:(A.get(j,0)+z*B.get(j,0))%p for j in A.keys()|B.keys()}))
    return U

def oriented(p,z):
    A,B=residue_inputs(p,z)
    if (A.degrees()[1],B.degrees()[1])!=(48,32):return None
    E=img(A,B,p) if compiler() else None
    if E is None:E=full_native(A,B,p)
    assert E and len(E)==7537
    return E

def images(p,z):
    U,V=(oriented(p,w) for w in (z,p-z))
    if U is None or V is None:return None
    p2,pz=pow(2,-1,p),pow(2*z,-1,p)
    return [[(a+b)*p2%p for a,b in zip(U,V)],[(a-b)*pz%p for a,b in zip(U,V)]]

def selected(shape,bnd):
    P=[];p=2**60;m=1
    while m<=2*bnd:
        p=int(nextprime(p+1000))
        if p%8!=7:continue
        z=pow(2,(p+1)//4,p);assert z*z%p==2
        P.append((p,z));m*=p
    return P,m

def exact():
    A,B=ab()
    bound=A[-1]**32*B[-1]**48
    P,MM=selected((48,32),bound)
    print('arith67 exact bounded CRT cap, bits, split-primes',7536,bound.bit_length(),len(P),flush=True)
    M=1;Z=[[0]*7537 for _ in range(2)]
    p,z=P[0]
    for t in (z,p-z):
        U,V=residue_inputs(p,t)
        assert oriented(p,t)==full_native(U,V,p)
    t0=perf_counter()
    for j,(p,z) in enumerate(P,1):
        W=images(p,z);assert W
        inv=pow(M,-1,p)
        for A,B in zip(Z,W):
            for i,v in enumerate(B):A[i]+=M*((v-A[i])*inv%p)
        M*=p
        if j%32==0 or j==len(P):
            print('arith67 exact CRT progress',j,M.bit_length(),round(perf_counter()-t0,2),flush=True)
    assert M==MM and M>2*bound
    for W in Z:
        for i,v in enumerate(W):
            if 2*v>=M:W[i]=v-M
        assert any(W) and all(abs(v)<=bound for v in W)
    G=images(65537,4080)
    assert G and all((a-b)%65537==0 for U,V in zip(Z,G) for a,b in zip(U,V))
    h=min(next(i for i,v in enumerate(W) if v) for W in Z)
    d=max(max(i for i,v in enumerate(W) if v) for W in Z)
    assert (d,h,bound.bit_length(),len(P))==(7536,693,29217,487)
    c=gcd(*(gcd(*W) for W in Z))
    print('arith67 exact outer up to common primitive scalar','cap',d,'valuation',h,
          'oriented degree',d-h,'all input degrees full',len(P),flush=True)
    with gzip.open('arith67-oriented-exact.gz','wt',encoding='utf-8') as f:
        for W in Z:
            for i in range(h,d+1):f.write(str(W[i]//c)+(' ' if i<d else '\n'))

if __name__=='__main__':exact()
