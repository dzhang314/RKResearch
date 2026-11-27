"""Exact fixed-stem exclusion on all eight-site precision-fourteen grids."""

from fractions import Fraction
from math import comb
from pathlib import Path
from itertools import zip_longest
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: check_eight_overlap.py REFINE_PORTS_WORKDIR MOVABLE_PORT_SOURCE_DIR")
sys.path.insert(0, str(Path(sys.argv[2]).resolve()))
from check_stem15 import I, B, Z, O, v, T, ev, construct

def psub(a, b):
    return [x-y for x,y in zip_longest(a,b,fillvalue=Z)]

def padd(a, b):
    return [x+y for x,y in zip_longest(a,b,fillvalue=Z)]

def pscale(a, s):
    return [s*x for x in a]

def div_root(p, z):
    r=[Z]*(len(p)-1)
    r[-1]=p[-1]
    for i in range(len(r)-2,-1,-1):
        r[i]=p[i+1]+z*r[i+1]
    assert not (p[0]+z*r[0]).sign()
    return r

def pcompose_legendre(n):
    # P_n(2Z - 1) = sum coefficient_i Z^i.
    return [(-1)**(n-i)*comb(n,i)*comb(n+i,i) for i in range(n+1)]

def powers_mod(p, cap):
    n=len(p)-1
    assert p[-1].sign()
    neg=[-s/p[-1] for s in p[:-1]]
    r=[O]+[Z]*(n-1)
    ret=[r]
    for _ in range(cap):
        r=padd([Z]+r[:-1],pscale(neg,r[-1]))
        assert len(r)==n
        ret.append(r)
    return ret

def hor_power_times(a, r, e):
    low=[Z]*len(r[0])
    for i,z in enumerate(a):
        low=padd(low,pscale(r[e+i],z))
    return low

def tr(M):
    return [list(c) for c in zip(*M)]

def rank_square(M):
    n=len(M); M=[r[:] for r in M]
    min_pivot=None
    for j in range(n):
        i=max(range(j,n),key=lambda i:M[i][j].inf())
        M[i],M[j]=M[j],M[i]
        p=M[j][j]
        assert p.sign(),f'could not certify pivot {j+1}/{n}'
        if min_pivot is None or p.inf()<min_pivot:
            min_pivot=p.inf()
        div=p.inv()
        for i in range(j+1,n):
            if M[i][j].lo==M[i][j].hi==0:
                continue
            u=M[i][j]*div
            for j2 in range(j+1,n):
                M[i][j2]=M[i][j2]-u*M[j][j2]
            M[i][j]=Z
    return min_pivot.bit_length()-1-B

p7,p8=(pcompose_legendre(n) for n in (7,8))
# Symmetry P_n(2(1-g)-1)=(-1)^n P_n(2g-1).
ref7=[-a for a in p7]
ref8=p8

# F(g,w)= P8(g w) P7(1-g) - P7(g w) P8(1-g).
fv=[Z]*16
for u,p,q in [(1,p8,ref7),(-1,p7,ref8)]:
    for k,pk in enumerate(p):
        for j,qj in enumerate(q):
            fv[k+j]=fv[k+j]+u*pk*qj*v**k
assert fv[0].sign() and fv[-1].sign()

_,_,Q,_=construct()
U=div_root(T(Q),v)
assert len(U)==7 and U[-1].sign()
assert ev(U,v).sign(),'the known shifted root is simple'

# Tensor-quotient basis g^i w^j, i=0..14, j=0..5. An invertible
# multiplication-by-F here rules out even complex common zeros.
R=powers_mod(fv,30)
S=powers_mod(U,13)
A=[hor_power_times(ref7,R,k) for k in range(23)]
B1=[hor_power_times(ref8,R,k) for k in range(22)]
factors=[]
for k in range(9):
    factors.append((p8[k],p7[k] if k<8 else 0))

cols=[]
for i in range(15):
    for j in range(6):
        out=[Z]*90
        for k,(a,b) in enumerate(factors):
            g=pscale(A[i+k],a)
            if b:
                g=psub(g,pscale(B1[i+k],b))
            w=S[j+k]
            out=padd(out,[gp*wp for gp in g for wp in w])
        cols.append(out)
print('Degree-15 port compatibility, degree-6 shifted-root quotient; check 90x90 multiplication matrix.',flush=True)
d=rank_square(tr(cols))
print('Exact full rank 90; all elimination pivots have magnitude at least 2^(%d).'%d)
print('No eight-site real precision-14 grid meets the reverse initial clock, fixed shared v, and any other shifted Q root.')
