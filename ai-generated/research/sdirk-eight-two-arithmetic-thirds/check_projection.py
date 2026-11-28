#!/usr/bin/env python3
"""A/A inverse-gap symmetric curve and primitive-anchor projection."""
from flint import fmpq_mpoly_ctx,fmpq,fmpq_poly
from math import gcd,lcm
Cx=fmpq_mpoly_ctx.get(('F','w'))
F,w=Cx.gens()
X=4*w*w*(2*F-w*w+1)
Y=-F*F+2*w*(5-w)*F-8*(w-1)
D=F*F
curve=(w*w-5*w+12-F)*(w*F+2)-16
T=-105*X*Y*D-15*X*D*D+175*Y**3+255*Y*Y*D+105*Y*D*D+9*D**3
p0=fmpq(3,7)*F*(-21*X*D+35*Y*Y+42*Y*D+15*D*D)
p1=-fmpq(3,7)*(-175*X*Y*D-21*X*D*D+245*Y**3+385*Y*Y*D+171*Y*D*D+15*D**3)
p2=-3*F*(-5*X*D+15*Y*Y+10*Y*D+3*D*D)
A=-63*X*X*Y*D*D+21*X*X*D**3-70*X*Y**3*D-210*X*Y*Y*D*D-138*X*Y*D**3-30*X*D**4+245*Y**5+805*Y**4*D+986*Y**3*D*D+546*Y*Y*D**3+129*Y*D**4+9*D**5
B=-525*X*X*Y*D*D+525*X*X*D**3-1750*X*Y**3*D-5670*X*Y*Y*D*D-3150*X*Y*D**3-630*X*D**4+3675*Y**5+13825*Y**4*D+17970*Y**3*D*D+9990*Y*Y*D**3+2259*Y*D**4+153*D**5
diag=180*A-F*B
class P:
 def __init__(self,e=0,o=0):
  self.e=Cx.constant(e) if isinstance(e,(int,fmpq)) else e
  self.o=Cx.constant(o) if isinstance(o,(int,fmpq)) else o
 def __bool__(self):return bool(self.e or self.o)
 def __add__(self,a):return P(self.e+a.e,self.o+a.o)
 def __neg__(self):return P(-self.e,-self.o)
 def __mul__(self,a):return P(self.e*a.e+X*self.o*a.o,self.e*a.o+self.o*a.e)
p=[P(0,p0),P(p1),P(0,p2),P(T)]
h=[P(2*F**3+6*Y*F-12*Y,-3*F*F),P(6*Y*F,-12*F),P(-12*F*F,3*F*F),P(2*F**3)]
def det(A):
 n=len(A);cur={0:P(1)}
 for line in A:
  nxt={}
  for key,y in cur.items():
   if not y:continue
   for i,c in enumerate(line):
    if key&(1<<i) or not c:continue
    nk=key|(1<<i)
    v=y*c
    if (key>>(i+1)).bit_count()%2:v=-v
    nxt[nk]=nxt.get(nk,P())+v
  cur=nxt
 return cur[(1<<n)-1]
def pad(b,i):return [P()]*i+b[::-1]+[P()]*(2-i)
H=det([pad(p,i) for i in range(3)]+[pad(h,i) for i in range(3)])
print('anchor even and odd degrees',H.e.degrees(),H.o.degrees(),flush=True)
R=(2-F)**2+Y
guard=F*w*X*T*p0*(R*R-X*(2-F)**2)*((R+4)**2-X*(2-F)**2)*((R-4+2*F)**2-X*(1-F)**2)
def paid(n):
 for p in (2,3,5,7):
  while n and n%p==0:n//=p
 return n
def scale(f,primitive=False):
 t=list(f.terms());L=lcm(*(int(a.denominator) for e,a in t))
 vals={e:int(a*L) for e,a in t}
 if primitive:
  d=gcd(*vals.values())
  if d:vals={e:c//d for e,c in vals.items()}
 else:assert paid(L)==1
 return Cx.from_dict(vals)
guard=scale(guard)
def trim(f):
 f=scale(f)
 while f:
  h=scale(f.gcd(guard),True)
  if h.is_constant():break
  assert all(c.denominator==1 for c in (guard/h).coeffs())
  f=f/h
  assert all(c.denominator==1 for c in f.coeffs())
 return f
def univar(a):
 vals=[0]*(a.degrees()[1]+1)
 for (j,i),b in a.terms():
  assert j==0
  vals[i]=b
 return fmpq_poly(vals)
PY=[trim(a) for a in (diag,H.e,H.o)]
proj=[univar(curve.resultant(a,'F')) for a in PY]
print('w projection degrees',[f.degree() for f in proj],flush=True)
common=fmpq_poly()
for p in proj:common=common.gcd(p)
assert [p.degree() for p in proj]==[38,93,82]
assert common==fmpq_poly([-1,1])**10
print('common projection',common)
v=[int(c*lcm(*(int(a.denominator) for a in common.coeffs()))) for c in common.coeffs()]
c=gcd(*v)
M=fmpq_poly([n//c for n in v])
pv=[]
for p in proj:
 a,r=divmod(p,M)
 assert not r and all(c.denominator==1 for c in a.coeffs())
 pv.append(a)
ns=gcd(*(abs(int(pv[0].resultant(q))) for q in pv[1:]))
print('AA outside common support bits',paid(ns).bit_length(),'value',paid(ns) if paid(ns).bit_length()<1500 else '--',flush=True)


assert paid(ns)==13**4*17*19*29*73**12*1193*43627**3
ev=[]
for a in (diag,H.e,H.o):
 z=a.subs({'w':1,'F':6})
 if z.is_constant():
  c=z.coeffs()[0] if z else fmpq(0)
 else:raise AssertionError(z)
 ev.append(abs(int(c.numerator)))
assert paid(gcd(*ev))==1
print('common w=1 support',1)
