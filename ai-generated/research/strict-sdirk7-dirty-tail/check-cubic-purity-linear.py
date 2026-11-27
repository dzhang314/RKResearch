#!/usr/bin/env python3
from fractions import Fraction as Q
from math import prod
import sys

INV = [
    [16,-120,240,-140],
    [-120,1200,-2700,1680],
    [240,-2700,6480,-4200],
    [-140,1680,-4200,2800],
]
H = [[Q(1,i+j+1) for j in range(4)] for i in range(4)]
assert [[sum(INV[i][k]*H[k][j] for k in range(4)) for j in range(4)]
        for i in range(4)] == [[int(i==j) for j in range(4)] for i in range(4)]

def dot(u,v):
    return sum(a*b for a,b in zip(u,v))

def replay(c):
    assert len(c)==6 and len(set(c))==6
    ell = [1/prod(c[i]-c[j] for j in range(6) if j!=i) for i in range(6)]
    assert all(w!=0 for w in ell)
    assert all(dot(ell,[x**k for x in c])==0 for k in range(5))
    def complete(v):
        u = -dot(ell[:4],v)
        w = -dot([L*x for L,x in zip(ell[:4],c[:4])],v)
        first = (w-c[5]*u)/((c[4]-c[5])*ell[4])
        second = (c[4]*u-w)/((c[4]-c[5])*ell[5])
        return v+[first,second]
    # Each possible four-coordinate input has a unique completion.
    # For each coordinate vector that completion is cubic interpolation.
    for i in range(4):
        v = [Q(k==i) for k in range(4)]
        w = complete(v)
        p = lambda y: prod((y-c[k])/(c[i]-c[k]) for k in range(4) if k!=i)
        assert w == [p(x) for x in c]
        assert dot(ell,w)==dot([x*l for x,l in zip(c,ell)],w)==0

if __name__ == '__main__':
    replay(list(map(Q,sys.argv[1:] or [0,2,5,1,-3,'9/7'])))
    print('Six-site cubic kernel and exact Hilbert inverse verified.')
