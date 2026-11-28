#!/usr/bin/env python3
"""Mixed A/Z: arithmetic chart solves k,q in (s,t), cubic v describes the opposite end."""
import sympy as S
from sympy import QQ,CRootOf,ring
from math import gcd,lcm
v0=S.Symbol('v')
Q=lambda x:4*x**3-12*x*x+3*x+2
K=QQ.algebraic_field(CRootOf(Q(v0),0))
v=K.from_sympy(CRootOf(Q(v0),0));o=K.one
R,s,t=ring('s,t',K)
D=1-t
F=(t+1)*(t+2)
A0=-D+2*t*t*(t+3)
k=(2-2*(s+1)*F)*D
q=(s+1)**2*A0-s*s*D-k*s
B=2-v;H=s*(1-v)-1;C=v*(2*s*s+2*s+1)+2*s
E=-H*k+B*q-C*D
# physical rear zero in original centered coordinates
z=1-(s+1)*(1+2*v)
x=k*k
T=-105*x*q-15*x*D+175*q**3+255*q*q*D+105*q*D*D+9*D**3
p0=3*k*(-21*x+35*q*q+42*q*D+15*D*D)/7
p1=-3*(-175*x*q-21*x*D+245*q**3+385*q*q*D+171*q*D*D+15*D**3)/7
p2=-3*k*(-5*x+15*q*q+10*q*D+3*D*D)
P=T*z**3+p2*z*z+p1*z+p0
A=-63*x*x*q+21*x*x*D-70*x*q**3-210*x*q*q*D-138*x*q*D*D-30*x*D**3+245*q**5+805*q**4*D+986*q**3*D*D+546*q*q*D**3+129*q*D**4+9*D**5
B=-525*x*x*q+525*x*x*D-1750*x*q**3-5670*x*q*q*D-3150*x*q*D*D-630*x*D**3+3675*q**5+13825*q**4*D+17970*q**3*D*D+9990*q*q*D**3+2259*q*D**4+153*D**5
diag=90*(s+1)*A-B
print('degree actual conic',E.degrees(),'pin',P.degrees(),'diag',diag.degrees(),flush=True)
r1=E.resultant(P);print('res pin',r1.degree(),flush=True)
r2=E.resultant(diag);print('res diag',r2.degree(),flush=True)
G=r1.gcd(r2)
assert (r1.degree(),r2.degree())==(39,53)
assert G==(r1.ring.gens[0]-1)**6
print('common guard power (t-1)^6',flush=True)


rr,x0=ring('X',QQ)
def prim(f):
 return sum((rr(c)*x0**j for j,c in enumerate(f.to_list()[::-1])),start=rr.zero)
M=sum((rr(c)*x0**j for j,c in enumerate(K.mod.to_list()[::-1])),start=rr.zero)
assert S.expand(M.as_expr().subs(x0.as_expr(),v0)-Q(v0))==0
M=M/4
assert S.expand(4*M.as_expr().subs(x0.as_expr(),v0)-Q(v0))==0
def norm(f):return abs(int(M.resultant(prim(f)).numerator))
def strip(x):
 for p in (2,3,5,7):
  while x and x%p==0:x//=p
 return x
rt=r1.ring.gens[0]
Gu=rt*(rt-1)*(rt+1)*(rt+3)*(2*rt*rt-1)*(4-9*rt*rt-3*rt**3)
Bad=1
def guard(P):
 global Bad
 for a in P.values():
  for c in a.to_list():Bad=lcm(Bad,int(c.denominator))
def trim(P):
 while P:
  g=P.gcd(Gu)
  if g.degree()==0:break
  guard(g);guard(Gu.exquo(g))
  P=P.exquo(g);guard(P)
 return P
f1,f2=trim(r1),trim(r2)
X0=f1.resultant(f2);guard(r1.ring(X0))
N0=strip(norm(X0))
print('pin and diagonal norm bit count',N0.bit_length(),flush=True)


R3,y,s3,t3=ring('y,s,t',K)
def lift(p):
 return R3.from_dict({(0,)+tuple(e):a for e,a in p.items()})
D3,k3,q3=map(lift,(D,k,q))
T3,p03,p13,p23=map(lift,(T,p0,p1,p2))
P3=T3*y**3+p23*y*y+p13*y+p03
H=2*D3*y**3+(3*k3-6*(s3+1)*D3)*y*y+(6*q3-6*(s3+1)*k3)*y+2*D3-3*k3+6*q3-6*(s3+1)*q3
ha0=P3.resultant(H)
print('front primitive anchor degrees',ha0.degrees(),flush=True)
ha=R.from_dict(ha0.to_dict())
r3=E.resultant(ha)
print('res front anchor in t',r3.degree(),flush=True)
f3=trim(r3)
w=f1.resultant(f3)
guard(r1.ring(w))
new=gcd(N0,strip(norm(w)))
print('check resulting support',new,'bits',new.bit_length(),'coordinate denominators',strip(Bad),flush=True)
assert r3.degree()==129
for f0 in (D,k,q,E,P,diag,ha,r1,r2,r3):guard(f0)
assert strip(Bad)==1
assert new==13**6*37**3*9767*9883*156347*383099*231631013129*1423306149647
print('complete supported characteristic product verified',flush=True)
