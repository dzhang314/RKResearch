#!/usr/bin/env python3
"""Universal exact two-return amplitudes used in the characteristic-zero construction."""
import sympy as S

def main():
    r=S.symbols('r')
    D=r*r-4*r+1;t=-r*(r+1)/D;W=5*r*r-14*r+5
    k=(r-S.Rational(1,2))/(3*(r-1)*(r-2))
    hv=r**3/(36*(r-1))
    ht=-r**3*(r+1)**2*(2*r-1)*W/(36*(r-1)*D**4)
    h=r*(r+1)/(r-1)**2
    q=9*(r-1)**2/(4*(r*r-r+1))
    n1=2*h/3;n2=4*q*h*h/9
    A=1+r+t;B=r+(1+r)*t
    Mc=lambda s:n2+(s-A)*n1+s*s-A*s+B
    E=[-k*Mc(1)/6,hv*Mc(r)/r,ht*Mc(t)/t]
    assert all(S.cancel(v-E[0])==0 for v in E)
    assert S.cancel(t**4/4-t**3*(1+r)/3+r*t*t/2+
                    3*(r-1)*(r-2)*ht)==0
    d0=3*(r-1)*(r-2)
    sig=S.Rational(1,6);p1=r**3/(6*(r-1));pr=r/2-p1/r
    assert S.cancel(p1+r**3*pr-r**4/4-d0*hv)==0
    D0=-2*sig;T=1/S.Integer(2)-D0/(r-1);Tr=D0/(r*(r-1))
    assert S.cancel(T+r**3*Tr-S.Rational(1,4)-S.Rational(3,2)*(sig+D0)-d0*k*D0)==0
    print("exact early repeated-pair, singleton, barycentric amplitudes and zero u diagonal")
if __name__=='__main__':main()
