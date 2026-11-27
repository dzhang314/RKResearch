#!/usr/bin/env python3
import sympy as S
u,m,n,y,c=S.symbols('u m n y c')
A=35*n*(5*n*n-3); B=15*(3*n*n-1); C=15*n*(5-7*n*n); D=9-15*n*n
gg=lambda y:A*(y-m)**3+B*m*(y-m)**2+C*m*m*(y-m)+D*m**3
P=S.Poly(gg(y),y)
a,b,d,e=[P.nth(k) for k in (3,2,1,0)]
R=S.factor(6*a+2*b+d+e)
Q=[(u-3)*(2*u*u-10*u+11),(u-3)*(u-2)*(2*u-3),4*(u-2)**2*(u-1),6*(u-1)**2*(2*u-3)]
F=sum(Q[k]*P.nth(k) for k in range(4))
G=6*(u-2)*(u-1)**2*(c-1)-3*(u-3)*(u-1)*(2*u-3)*c*(c-2)+(u-3)*(u-2)**2*c*c*(c-3)

def projectively_rootless(P,variable,degree,p):
    f=S.Poly(P,variable,domain=S.ZZ)
    assert f.degree()==degree and int(f.LC())%p
    assert all(int(f.eval(i))%p for i in range(p))

F0=S.cancel(F.subs(n,0)/(6*m))
R0=S.factor(S.resultant(F0,G.subs(c,m),m))
octic=S.cancel(R0/(2*(u-3)**2*(u-2)**2*(u-1)**3))
projectively_rootless(octic,u,8,13)
late=S.Poly(S.cancel(m**3*F.subs({u:S.Rational(53,31),n:11/m-1})),m).clear_denoms()[1].primitive()[1]
projectively_rootless(late.as_expr(),m,6,17)

M=u*u-4*u+2
T=u**3-7*u*u+10*u-2
J=4*u**3-24*u*u+39*u-17
for poly,degree,p in [(M,2,3),(T,3,3),(J,3,5)]:
    projectively_rootless(poly,u,degree,p)
assert S.expand(R.subs(n,0)+6*m*(m*m-5*m+5))==0
print("centered fourth placement excluded by the primitive octic modulo 13")
print("known (u,e)=(53/31,11) fourth placement excluded by the sextic modulo 17")
