#!/usr/bin/env python3
import sympy as S
from sympy.polys.rings import ring
v=S.symbols('v')
H=v**3-4*v**2-v+2
assert S.Poly(H,v).is_irreducible
K=S.QQ.algebraic_field((S.Poly(H,v),v))
R,T,D=ring('T,D',K)
V=R.one*K.unit
one=R.one;zero=R.zero
for d in (0,1):
 a=one*(d+1);h=D-1-V;s=D-1
 P3=(T-a)*(T-h)*(T-s)
 I=lambda P:sum((c*D**(i+j)*K.convert(S.Rational(1,i+1)) for (i,j),c in P.items()),zero)
 J=lambda P:sum((c*T**(i+1)*D**j*K.convert(S.Rational(1,i+1)) for (i,j),c in P.items()),zero)
 m0,m1,m2,m3,m4=(I(P3*T**j) for j in range(5))
 delta=m0*m2-m1*m1
 g0=m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2)
 Q2=delta*T*T+(m1*m2-m0*m3)*T+(m1*m3-m2*m2)
 r=T**d
 L=70*T**4-140*D*T**3+90*D*D*T*T-20*D**3*T+D**4
 ev=lambda P,a:sum((c*a**i*D**j for (i,j),c in P.items()),zero)
 g=ev(L,a)*(a*J(r)-J(T*r)+(T-a)*r)-L*(a*ev(r,a)-ev(J(T*r),a))
 w=Q2.resultant(g)
 uu=g0.drop(T)
 selw=w.gcd(uu);selp=delta.drop(T).gcd(uu)
 SD=selw.ring
 x=SD.gens[0]
 lf=x**4-20*x**3+90*x*x-140*x+70
 assert selw.monic()==(x**6*lf if d==0 else x**6)
 assert selp.monic()==x**2
 print('monomial',d,'regular factor',selw.monic().as_expr(),'singular factor',selp.monic().as_expr(),flush=True)
