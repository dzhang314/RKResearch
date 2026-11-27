#!/usr/bin/env python3
"""Independent polynomial and partial-tableau replay of the rank-two reads."""
from functools import lru_cache
from math import prod
import sympy as S

t,w,r=S.symbols('t w r')
a=-(t-2)*(t-1)**2
b=2*t*(t-2)*(2*t-1)
c=-2*t*t*(t-1)
F=2*a*(w**3-3*w**2)+3*b*(w*w-2*w)+6*c*(w-1)
H=a*w*w+2*b*w+6*c
U=t**6-19*t**5+112*t**4-218*t**3+41*t*t+121*t-54
assert S.expand(S.resultant(F,H,w)-48*t**4*(t-2)**2*(t-1)**3*U)==0
assert S.Poly(U,t).LC()%5 and all(U.subs(t,j)%5 for j in range(5))
A=S.Matrix([[1,0,0],[t,1,0],[w-r,r,1]])
x=A*S.ones(3,1)
C=S.diag(*x)
R=C*A-A*C-A*A
assert S.expand(((A*R-R*A)*S.ones(3,1))[2]-r*t*(2*t-w))==0
g=-R*S.ones(3,1)
k=lambda x:1+2*x-x*x
assert S.expand(g[2]-(k(w)+2*r*t))==0
assert S.expand(S.factor(F.subs(w,2*t/(3*t-2)))+
    4*t**3*(t-2)*(t-1)*(31*t-22)/(3*t-2)**3)==0

@lru_cache(None)
def size(T):
    return 1+sum(map(size,T))
@lru_cache(None)
def trees(n):
    if n==1:
        return ((),)
    pool=tuple(t for j in range(1,n) for t in trees(j))
    def choose(start,left):
        if left==0:
            yield ()
        for j in range(start,len(pool)):
            t=pool[j]
            if size(t)>left:
                break
            for s in choose(j,left-size(t)):
                yield (t,)+s
    return tuple(choose(0,n-1))

# Four unit-diagonal Euler steps, then a reflection-breaking, quartic-clean zero site.
Q=[[int(j<=i) for j in range(5)] for i in range(4)]+[[-4,6,-4,1,1]]
assert [sum(row) for row in Q]==[1,2,3,4,0]
@lru_cache(None)
def stage(T):
    return tuple(prod(sum(v*w for v,w in zip(row,stage(U))) for U in T) for row in Q)
assert sum(map(lambda n:len(trees(n)),range(1,6)))==17
assert stage(())[4]==1
assert all(stage(T)[4]==0 for n in range(2,6) for T in trees(n))
print('Double-read elimination and all 17 first-active partial stage profiles checked.')
