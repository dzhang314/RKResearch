#!/usr/bin/env python3
"""Two exactly split interpolants, but provably unsplit residual cubics."""
from flint import fmpq,fmpq_poly,nmod_poly
from math import prod, lcm
from sympy import primerange
P=lambda *x:fmpq_poly(list(x))
X=P(0,1);F=fmpq

def core(tag,c,h):
    # z=2, m=1, u=0 in both cases.
    if tag=="reflection":
        suffix=[4,0,1];rates=[1,1,F(-1,2)]
        G=(X**3-9*X*X+18*X-6)/6
        E=1+X/3
    else:
        suffix=[-1,0,1];rates=[F(17,2),1,F(-1,2)]
        G=(X-1)-F(9,2)*(X*X/2-X)+3*(X**3/3-X*X)
        E=1-X/2
    R3=prod([X-y for y in suffix],start=P(1))
    Q3=(X-1)**3-F(3,5)*(X-1)
    Q4=(X-1)**4-F(6,7)*(X-1)**2+F(3,35)
    interp=lambda p:sum(((R3//(X-y))*p(y)/((R3//(X-y))(y)*r) for y,r in zip(suffix,rates)),start=P(0))
    T3,T4=interp(Q3),interp(Q4)
    A,ar=divmod(G*T3+E*Q3,R3)
    B,br=divmod(G*T4+E*Q4,R3)
    assert not ar and not br
    delta=-B(c)/A(c)
    T=T4+delta*T3;g=Q4+delta*Q3
    W=X-h
    assert T%W==0 and all(W(y) and T(y) and g(y) for y in suffix+[c])
    J=lambda p:sum((F(2**i,i+1)*p[j]*X**(j-1-i) for j in range(1,len(p)) for i in range(j)),start=P(0))
    H=J(g)
    unit,C,D=(H*R3).xgcd(g)
    assert unit.degree()==0
    step=(-W*T*C/unit[0])%g
    tau=-g(c)/step(c)
    S4=g+tau*step
    assert S4(c)==0
    assert g*J(R3*S4)-H*R3*S4==tau*W*T
    S3=S4//(X-c)
    clear=lcm(*(int(v.denominator) for v in S3.coeffs()))
    data=[int(v*clear) for v in S3.coeffs()]
    ps=[q for q in primerange(2,100) if (s:=nmod_poly(data,q)).degree()==3 and not s.roots()]
    assert ps
    print(tag,'z=2,u=0,c=',c,'h=',h,'delta=',delta,'tau=',tau,'residual cubic projectively rootless modulo',ps[0])

if __name__=="__main__":
    core("reflection",F(1942,1399),F(-3))
    core("arithmetic",F(-186,83),F(2))
