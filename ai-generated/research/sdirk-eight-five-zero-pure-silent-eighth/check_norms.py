#!/usr/bin/env python3
import sympy as S
from math import gcd
u,v,T=S.symbols('u v T')
Q=u**3-3*u**2+S.Rational(3,4)*u+S.Rational(1,2)
H=v**3-4*v**2-v+2
red=lambda f:S.rem(S.rem(S.expand(f),Q,u),H,v)
def norm(f):
 a=S.rem(S.resultant(Q,red(f),u),H,v)
 return S.resultant(H,a,v)
def paid(f,vs):
 for c in S.Poly(f,*vs).coeffs():
  d=int(S.denom(c))
  for p in (2,3,5,7):
   while d%p==0:d//=p
  assert d==1
def stripped(n):
 n=abs(int(S.numer(n)))
 for p in (2,3,5,7):
  while n%p==0:n//=p
 return n
def I(P,D):return red(sum(c*D**i/(i+1) for (i,),c in S.Poly(P,T).terms()))
def J(P):return S.integrate(P,(T,0,T))
def L(T,D):return 70*T**4-140*D*T**3+90*D**2*T*T-20*D**3*T+D**4
A=1+2*u
r=(T-1)*(T-1-u); J0=J(r);J1=J(T*r)
for typ,D in [('one',2+2*v),('two',2+u+2*v)]:
 P=(T-A)*(T-(D-1-v))*(T-(D-1))
 m=[I(P*T**j,D) for j in range(5)]
 m0,m1,m2,m3,m4=m
 delta=red(m0*m2-m1*m1)
 h=red(m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2))
 # Equivalent to the allowed quadratic node polynomial times its Cramer pivot.
 c=delta*T*T+red(m1*m2-m0*m3)*T+red(m1*m3-m2*m2)
 p0=A*J0-J1+(T-A)*r
 p1=A*r.subs(T,A)-J1.subs(T,A)
 g=L(A,D)*p0-L(T,D)*p1
 gg=S.Poly(g,T)
 g=sum(red(gg.nth(i))*T**i for i in range(5))
 # Form explicit Sylvester resultant, then reduce in v,u before norms.
 pp=red(S.resultant(c,g,T))
 nh=norm(h);ng=norm(pp);ns=norm(delta)

 for f in (delta,h,c,g,pp,nh,ng,ns):paid(f,(u,v,T))
 assert nh!=0 and ng!=0 and ns!=0
 print(typ,"norms",nh,ng,ns,flush=True)
 G1=gcd(stripped(nh),stripped(ng))
 G2=gcd(stripped(nh),stripped(ns))
 assert (G1,G2)==((17,1) if typ=="one" else (62753**6,62753**2))
 print(typ,"regular and singular common stripped supports",G1,G2,flush=True)
