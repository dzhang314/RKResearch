#!/usr/bin/env python3
from gate_scan import ctx,phase,twozero,three_two_clocks
from itertools import permutations

def values(F,a,b):
    k=a+b-2
    q=(a+b)*k-a*b+9*F.one()/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x**3/3+k*x*x/2+q*x
    jx=lambda x:x**4/4+k*x**3/3+q*x*x/2
    return k,q,r,j,jx

def rear(F,a,b,g):
    k,q,r,j,jx=values(F,a,b)
    R=r(1-g)
    if R==0:return ['zero terminal graph']
    kR=-2-k
    K0=R+g*g
    K1=2*R-g*(2*g+kR)
    if K0==0:
        return ['gap free'] if K1==0 else []
    u=K1/K0
    t=[]
    for br,w,kg,r3 in phase(u):
        if kg!=0 and R*kg==r(1-g*(1+w)):
            t.append(('offzero',br,u,w,r3))
        if kg==0 and 1-g*(1+w)==b:
            t.append(('zero-at-8',br,u,w,r3))
    return t
