#!/usr/bin/env python3
"""Small exact algebraic calibrations, not a search for quadrature supports."""
from fractions import Fraction as F
from math import prod


def need(c,what):
    if not c: raise AssertionError(what)


def mul(p,q):
    z=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):
            z[i+j]+=x*y
    return z


def av(p,x):
    v=F(0)
    for y in p[::-1]: v=v*x+y
    return v


def norm(a,b):
    return b-a-1,a*(2*b+1),4*a*b*(a-b),-4*a*a*b*(b+1)


def sigma(a,b): return (a+b-1)**3+27*a*b


def quartic(a,b):
    s=a+b-1
    return [a*a,-2*a*(s+2),s*s+6*a,2*s-4*a,F(1)]


def division_by_root(p,r):
    q=[F(0)]*(len(p)-1)
    for i in range(len(q)-1,-1,-1):
        q[i]=p[i+1]+(r*q[i+1] if i+1<len(q) else 0)
    need(p[0]+r*q[0]==0,"exact root division")
    return q


def f(a,b,x): return x+a/x+b/(x-1)


def finite(a,b):
    x,y,z=a*(b+1)/(a-b),(a-b)/(a+1),(a+1)/(b+1)
    need(len({x,y,z})==3 and not ({x,y,z}&{F(0),F(1)}),"explicit admissible normalized triple")
    s=f(a,b,x)
    need(f(a,b,y)==s==f(a,b,z),"single fibre")
    need(mul(mul([-x,1],[-y,1]),[-z,1])==[-a,s+a+b,-1-s,1],"literal cubic factorization")
    al,be,eta,theta=norm(a,b)
    g=x*x+al*x+be
    need(av(quartic(a,b),x)==g*g and eta*x+theta==0,"negative infinity has finite quartic point")
    U=2*x*(x-1)*y-(x*x+(a+b-1)*x-a)
    need(U==-g,"correct second branch, not just square value")
    return (x,y,z)


def model(a,b):
    al,be,e,t=norm(a,b)
    A,B,C=al*al-4*be,2*al*e-4*t,e*e
    def on(P):
        if P is None: return True
        x,y=P
        return y*y==x**3+A*x*x+B*x+C
    def add(P,Q):
        if P is None: return Q
        if Q is None: return P
        x,y=P
        u,v=Q
        if x==u and y+v==0: return None
        s=(3*x*x+2*A*x+B)/(2*y) if P==Q else (v-y)/(u-x)
        X=s*s-A-x-u
        Y=-y+s*(x-X)
        need(on((X,Y)),"exact elliptic addition")
        return X,Y
    def times(n,P):
        Q=None
        while n:
            if n%2: Q=add(Q,P)
            P=add(P,P)
            n//=2
        return Q
    D=(F(0),-e)
    T=(4*a*b,4*a*b)
    need(on(D) and on(T) and times(3,T) is None,"3-torsion coordinate")
    return times,D,T


a,b=F(1),F(2)
need(sigma(a,b)!=0,"smooth probe")
print("Smooth normalized model (a,b)=(1,2): rank-free finite triple",
      tuple(map(str,finite(a,b))))
times,D,T=model(a,b)
need(all(times(n,D) is not None for n in (6,9,12)),"exact nontorsion test")
print("Good elliptic probe: [3]T=0; none of [6]D,[9]D,[12]D vanishes.")
a,b=F(2),F(2)
times,D,T=model(a,b)
need(times(2,D) is None and D is not None,"symmetric 2-torsion infinity difference")
print("Symmetric probe a=b=2: the second infinity difference is 2-torsion.")

a,b=F(27),F(-8)
r=F(3)
need(sigma(a,b)==0 and a==r**3 and b==(1-r)**3,"one triple-point chart")
Q=division_by_root(division_by_root(quartic(a,b),r),r)
need(len(Q)==3 and Q[-1]==1 and Q[1]**2-4*Q[0]!=0,"squarefree conic normalization")
print("One-node degeneration: monic quadratic normalization; finite triple",
      tuple(map(str,finite(a,b))))
a=b=F(-1)
need(quartic(a,b)==mul([1,-1,1],[1,-1,1]),"double triple-point identity")
x=F(2)
trip=(x,1/(1-x),(x-1)/x)
need(len(set(trip))==3 and len({f(a,b,z) for z in trip})==1,"Möbius cyclic rule")
print("Cyclic a=b=−1 degeneration: both residual roots given by the Möbius cycle.")

points=[F(0),F(1),F(1,3),F(4,5)]
masses=[F(5,48),F(1,24),F(27,56),F(125,336)]
errors=[sum(w*x**j for x,w in zip(points,masses))-F(1,j+1) for j in range(6)]
need(errors==[0,0,0,0,0,F(-1,900)] and all(w>0 for w in masses),
     "target-order gap-one counterexample seed")
print("Gap-one countercheck: positive rational four-site order exactly five.")
print("PASS: exact identities only; no rational support scan and no Lean.")
