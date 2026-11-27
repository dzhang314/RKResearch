"""Replay the small algebraic gates in all rational repeat chronologies.

Uses exact rational arithmetic and SymPy rational-function normalization.
The finite loops use mathematical bounds in the companion proof, not
height cutoffs for unresolved charts.
"""
from fractions import Fraction as F
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path

import sympy as sp

def compact(x):
    return sp.factor(x) if isinstance(x,sp.Expr) else x

def H_values(sites):
    return [compact(-(sum(q)/3)-prod(q)) for i in range(4)
            for q in [[x for j,x in enumerate(sites) if j!=i]]]

def W_values(sites):
    return [compact(h/prod(x-y for j,y in enumerate(sites) if j!=i))
            for i,(x,h) in enumerate(zip(sites,H_values(sites)))]

def k(a,x):
    return (1+2*x+4*a*x-2*a*a-x*x)/(a+1)**2

def h(a):
    return (5*a*a-3)/(5*(1-3*a*a))

def Q4(a):
    return 15*a**4+30*a**3+24*a*a+10*a+2

def P6(a):
    return 15*a**6-34*a**4-10*a**3+22*a*a+14*a+2

def D5(a):
    return 30*a**5+45*a**4+12*a**3-10*a*a-6*a-1

def N6(a):
    return 30*a**6+15*a**5-46*a**4-30*a**3+14*a*a+13*a+2

def norm(sites, alpha, duplicate, d, e):
    H=H_values(sites)
    W=W_values(sites)
    mu=[compact(alpha/v) for v in H]
    j=duplicate
    core=compact(sum(compact(w*q*q) for w,q in zip(W,mu)))
    return compact(core+compact(W[j]*(d-mu[j])*(mu[j]-e)))

def check_identities():
    a,r,u,w=sp.symbols("a r u w")
    s=compact(h(a)/r)
    T=[a,r,s,-a]
    A,R,_,B=H_values(T)
    sm=5*(3*a*a-1)*r*r-5*a*a-4*a*r+3
    ss=sm+8*a*r
    expected24=4*sm*(Q4(a)*r*r-P6(a))/(3*(a+1)**4*(5*(3*a*a-1)*r*r+5*a*a-3)*ss)
    expected25=-4*sm*(N6(a)+D5(a)*r)/(3*(a+1)**2*(3*a*a-1)*(5*a*a-3)*
        (15*a**3*r-5*a*a-5*a*r+3)*(2*a*a+4*a*r+r*r+2*r-1))
    assert sp.cancel(A + sm/(15*r*(3*a*a-1)))==0
    assert sp.cancel(B + ss/(15*r*(3*a*a-1)))==0
    assert sp.cancel(norm(T,A,1,k(a,r),k(a,-r)*A/B)-expected24)==0
    assert sp.cancel(norm(T,A,3,k(a,-a),A/(R*k(a,-r)))-expected25)==0
    v=compact((-sp.Rational(3,5)-u*w)/(u+w))
    T=[sp.S(0),u,v,w]
    J=H_values(T)
    alpha=J[1]*k(0,u)
    lam=J[3]*k(0,-w)/alpha
    expected15=-4*(5*w*w-3)*(u*u-2*u-1)*(2*u*w-u+w-2)/(3*(5*u*u-3)*(5*u*w+3)*(w*w+2*w-1))
    assert sp.cancel(norm(T,alpha,0,1,1/lam)-expected15)==0
    U=u*u+u+1; V=(u+3)*(5*u+1)
    assert sp.expand((-11*u-13)*V+(55*u+186)*U-147)==0
    assert sp.cancel(v.subs(w,(u+2)/(2*u+1))+V/(10*U))==0

def smooth(n):
    n=abs(n)
    if not n:return False
    for q in (2,3,5):
        while n%q==0:n//=q
    return n==1

def paid(q):
    return smooth(q.denominator)

def weights_fail(T):
    return not all(map(paid,W_values(T)))

def check_15():
    candidates={}
    for n in range(1,15):
        if not smooth(n):continue
        for m in range(-14,15):
            if gcd(m,n)!=1 or m*m+m*n+n*n not in (1,3,7,21,49,147):continue
            u=F(m,n)
            if 2*u+1==0:continue
            w=(u+2)/(2*u+1)
            v=-(u+3)*(5*u+1)/(10*(u*u+u+1))
            T=[F(0),u,v,w]
            if len(set(T))!=4 or not all(map(paid,T)):continue
            assert weights_fail(T)
            candidates[u]=(v,w)
    assert set(candidates)=={F(4),F(-13,2),F(1,2),F(-2,3),F(-5,4),F(-3,8)}
    print("Pair (1,5): all six bounded parameter candidates eliminated by weights.")

def check_diagonal_cases():
    squares17={v*v%17 for v in range(17)}
    assert {B for B in (-1,2,3,-6) if -B%17 in squares17}=={-1,2}
    assert Q4(0)==P6(0)==2 and (D5(0),N6(0))==(-1,2)
    assert 2+F(-3,10)==F(17,10)
    xy=[(1,1)]
    for _ in range(5):
        x,y=xy[-1]
        xy.append((2*x+3*y,x+2*y))
    assert xy[-1][1]>17*11
    for j in range(1,6):
        x,y=xy[j]
        assert x*x-3*y*y==-2
        assert y>2*j+1 or j==1
    assert [(x,y) for x,y in xy if y%17==0 and y<=17*11]==[(265,153)]
    assert 265%53==0
    return {F(1),-F(5,9),*(e*F(1,d) for e in (-1,1) for d in (2,3)),
            *(e*z for e in (-1,1) for z in (F(2,3),F(3,5)))}

def check_24_25():
    d=check_diagonal_cases()
    carries_square=[]
    good_clocks=[]
    for a in sorted(d):
        assert a and smooth(a.numerator) and smooth(a.denominator)
        assert smooth((a+1).numerator)
        assert Q4(a) and D5(a) and N6(a)
        H=h(a)
        u2=F(P6(a),Q4(a))
        if u2>=0:
            m,n=isqrt(u2.numerator),isqrt(u2.denominator)
            if (m*m,n*n)==(u2.numerator,u2.denominator):
                assert m
                carries_square.append(a)
                for r in (F(m,n),-F(m,n)):
                    T=[a,r,H/r,-a]
                    assert len(set(T))==4 and weights_fail(T)
        r=-F(N6(a),D5(a))
        T=[a,r,H/r,-a]
        if len(set(T))==4 and all(map(paid,T)):
            good_clocks.append(a)
            assert W_values(T)[0]=={F(-2,3):F(93,232),F(-1,2):F(8,19)}[a]
            assert not paid(W_values(T)[0])
    assert set(carries_square)=={F(-2,3),F(1)}
    assert set(good_clocks)=={F(-2,3),F(-1,2)}
    print("Pair (2,4): all square cases excluded. Pairs (2,5),(1,4): both paid-clock cases excluded.")

def main():
    central=Path(__file__).with_name("verify-order-five-paid-central-repeat-exclusion.py")
    run_path(str(central))["main"]()
    print("Pairs (3,4),(2,3),(3,5),(1,3): same initial singleton gate and aggregate weights.")
    check_identities()
    check_15()
    check_24_25()
    print("All exact scalar replay checks passed.")

if __name__=="__main__":
    main()
