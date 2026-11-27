#!/usr/bin/env python3
import sympy as s
from sympy.polys.fields import field
from sympy import QQ
from sympy.polys.rings import ring
from flint import fmpq_poly,fmpq
K,m,v=field('m v',QQ)
h=K(1)/2
beta=3-m
b=m-2
t0=1-m;t1=m-1;r=2-v
n=3*m*m/5
L3=lambda t:t*(t*t-n)
L4=lambda t:t**4-6*m*m*t*t/7+3*m**4/35
P3=lambda t:(t-beta)*((t-beta)**2-4)
a2=-6*m*m/7
a0=3*m**4/35
s0=2*(a0+3*beta**4-12*beta*beta)
s1=-16*beta*(beta*beta-1)
s2=2*(a2+6*beta*beta+4)
S=lambda t:s0+s1*t+s2*t*t
sp=s1+2*b*s2
lp=4*b*(b*b+v)+2*a2*b
gR=lp/sp
H=gR/r
Lavg=b**4+6*b*b*v+v*v+a2*(b*b+v)+a0
Savg=S(b)+s2*v
J=(Lavg/r-L4(t1)-H*(Savg-S(t1)))/(r-1)
B=J/(H*H)
f=L4(t1)-H*S(t1)-J*(1-h/H)
g4=-2*L4(t0)/B
C0=-L3(t0)/(h*g4) # C0 here is evaluation of the affine C at t0, not at zero
def row(p3,l3,T,g,df=False):
  w=g*(g-h)
  return [g/h*p3, -w*T, -(1-g/h)*l3+(K.zero if df else w*C0)]
r1=row(P3(t1),L3(t1),t1-t0,H)
r2=row(P3(b)+(3*b-3*beta)*v,L3(b)+3*b*v,b-t0,gR)
r3=row(3*(b-beta)**2+v-4,3*b*b+v-n,K.one,gR,True)
det=sum((r1[j]*(r2[(j+1)%3]*r3[(j+2)%3]-r2[(j+2)%3]*r3[(j+1)%3]) for j in range(3)),start=K.zero)
def as_expr(p):return p.as_expr()
def ff(p):return [(q,e) for q,e in s.factor_list(as_expr(p))[1]]
assert [(str(t),e) for t,e in ff(sp.numer)]==[('m - 2',1),('32*m**2 - 224*m + 371',1)]
guards=sp*H*B*(g4-h)*g4*v*(v-1)*r
def remove(p,kind):
 out=[]
 for a,e in ff(p):
  q=K(a)
  if q.numer.gcd(guards.numer*guards.denom).degree() > 0:
   assert a==4*s.Symbol('m')**2-28*s.Symbol('m')+7*s.Symbol('v')+28
  else:out.append(a)
 return out
fs=remove(f.numer,'F');gs=remove(det.numer,'V')

assert sorted(s.degree(q,s.Symbol('v')) for q in fs)==[1,1]
assert sorted(s.degree(q,s.Symbol('v')) for q in gs)==[0,1,1,3]
