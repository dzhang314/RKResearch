"""Small exact rational vector and polynomial helpers."""
from functools import reduce
import operator

def mul(V,W):
    out=[0]*(len(V)+len(W)-1)
    for i,a in enumerate(V):
        for j,b in enumerate(W):
            out[i+j]+=a*b
    return out
def product(seq):
    return reduce(operator.mul,seq,1)
def hull(nodes):
    return reduce(mul,([-v,1] for v in nodes),[1])
def scale(f,a):
    return [a*v for v in f]
def val(f,v):
    return reduce(lambda hi,lo:v*hi+lo,reversed(f),0)
def integ(f,v):
    z=0
    for i,a in enumerate(f,1):
        z+=a*v**i/i
    return z
def interp(nodes):
    return [scale(hull([v for j,v in enumerate(nodes) if j!=i]),
                  1/product(u-v for j,v in enumerate(nodes) if j!=i))
             for i,u in enumerate(nodes)]
def quad(nodes,v):
    return [integ(f,v) for f in interp(nodes)]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def matrix_vec(M,v):return [dot(r,v) for r in M]
def solve(M,b, one):
    # All casts stay in the chosen ring. Divisions apply only to a nonzero pivot.
    n=len(b); assert len(M)==n and all(len(r)==n for r in M)
    T=[list(r)+[z] for r,z in zip(M,b)]
    for j in range(n):
        i=next((i for i in range(j,n) if T[i][j]),None)
        if i is None: raise ValueError("singular solve")
        T[i],T[j]=T[j],T[i]; t=one/T[j][j]
        T[j]=[z*t for z in T[j]]
        for i in range(n):
            if i!=j and T[i][j]:
                k=T[i][j];T[i]=[a-k*c for a,c in zip(T[i],T[j])]
    return [r[-1] for r in T]
def add(a,b):return [u+v for u,v in zip(a,b)]
def diff(a,b):return [u-v for u,v in zip(a,b)]
