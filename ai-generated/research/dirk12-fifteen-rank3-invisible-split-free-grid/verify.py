#!/usr/bin/env python3
"""Exact arithmetic replay for split-free DIRK12/15 grid and mixed filters."""
import sympy as S
from grid import (
    F, card_taps, diff_lag, forward_pair, mixed_grid, reverse_seed,
    reverse_hull_from_moments, third_and_next_ratios,
)


def eq(a,b=0):
    assert S.cancel(a-b)==0,S.factor(a-b)


def main():
    r,d,q=S.symbols('r d q')
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    nodes=[S.Integer(1),r,t]
    def moments(head,jmax):
        return [S.factor(sum(s**j/(h*S.prod(s-z for a,z in enumerate(nodes) if a!=i))
                     for i,(s,h) in enumerate(zip(nodes,head))))
                for j in range(jmax+1)]
    m10=moments([S.Rational(1,6),g,h10],4)
    m9=moments([-k/6,hv,h9],5)
    common=-6*(r-1)*(r-2)/(2*r-1)
    for a,b in zip(m9[1:],m10):eq(a,common*b)
    lam=(r-1)**2/r
    q0=S.Rational(9,4)*lam/(lam+1)
    a,b,c,e,f=m10
    eq(a*c/b**2,q0)
    eq(b*e/c**2,2/(3-q0))
    eq(c*f/e**2,S.Rational(5,2)*(3-q0)/(9-4*q0))
    eq(b/a,S.Rational(2,3)*r*(r+1)/(r-1)**2)
    ra=m9[0]*m9[2]/m9[1]**2
    eq(ra,(4*q0-3)*(5-2*q0)/(3*q0))
    h=S.Rational(3,2)*d*b/a
    eq(h*lam,d*(1+r))
    eq(h*h*lam*lam/(lam+4),d*d*r)
    eq(-h*lam/(lam-2),d*t)
    eq((r*r-4*r+1)/r,lam-2)
    eq((5*r*r-14*r+5)/r,5*lam-4)
    eq(q0.subs(r,2),S.Rational(3,4))
    eq(q0.subs(r,-1),3)
    print("exact early barycentric power sums and all scale-only tests")
    for chart,duplicate,mu in [(10,False,m10),(9,False,m9[1:]),(9,True,m9[:5])]:
        raws=[c*d**i for i,c in enumerate(mu)]
        (s,p,u),q1,rs=reverse_hull_from_moments(raws,chart,duplicate)
        for a0,b0 in zip((s,p,u,q1),(d*(1+r),d*d*r,d*t,q0)):eq(a0,b0)
        for x in rs:eq(x)
    rz=-4+S.sqrt(15)
    m0=S.simplify(m9[0].subs(r,rz))
    assert m0==0
    num=[S.simplify(x.subs(r,rz)) for x in m9[:5]]
    out,_,cs=reverse_hull_from_moments(num,9,True)
    assert all(S.simplify(a-b)==0 for a,b in zip(out,(1+rz,rz,t.subs(r,rz))))
    assert all(S.simplify(x)==0 for x in cs)
    print("same unordered cubic for all three endpoint cases, including exact m0=0")
    delta=S.symbols('delta')
    sig=S.Rational(1,6)
    td=S.Rational(1,2)-delta/(r-1)
    tr=delta/(r*(r-1))
    e2=(td+tr*r**5-S.Rational(1,6)-2*(sig+delta))/(k*delta)
    eq(e2,(r**3+r*r+r-1)/k)
    # The optional fourth distinct reverse zero has no deweighting.
    rs,E,Z,diag=third_and_next_ratios(9,r,S.Integer(0))
    eq(E[-1],L*((1+r+t)**2-(r+t+r*t)))
    eq(diag)
    pol=S.factor(S.together(
         ((r*r+r-F(4,5))/k
           - ((r**3/(6*(r-1))+(r/2-r*r/(6*(r-1)))*r**4-r**5/5)/hv))/(r-1)
         +(r*r+r-F(4,5))/k-(1+r+t)*L))
    eq(pol,9*r*(r-1)*(r+1)*(3*r*r-7*r+3)/(5*(2*r-1)*(r*r-4*r+1)))
    qnum,qden=S.fraction(S.cancel(q0-S.Rational(9,16)))
    assert S.rem(qnum,3*r*r-7*r+3,r)==0
    print("literal pair-split cancellation and optional fourth reflected-zero gate")
    for chart,f_f in [(9,F(3,2)),(9,F(3)),(10,F(3,2))]:
        output=mixed_grid(F(1,3),F(4,5),F(9,7),F(7,5),f_f,F(1,20),F(3,20),chart)
        assert output['epsilon12'] !=0 and output['ordinary_gamma_nonzero'] !=0
        assert output['reverse_Z_nonzero']!=0 and output['third_diagonal']==0
        assert any(output['quadrature'])
    aa,gg=forward_pair(F(1,2),F(3,4),F(7,6),True)
    assert aa==F(966996,5768035) and gg==F(-685376,8075249)
    print("three rational negative-control grid paths, including nonzero unpaid epsilon12")


if __name__=='__main__':
    main()
