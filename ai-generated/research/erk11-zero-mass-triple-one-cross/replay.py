from itertools import combinations,product
from collections import Counter
import re
from pathlib import Path
S=10**54
class I:
 def __init__(self,lo,hi=None,scale=1):
  self.a=lo*S//scale;self.b=(hi if hi is not None else lo)*S//scale
 @staticmethod
 def raw(a,b):return I(a,b,S)
 @staticmethod
 def co(x):return x if isinstance(x,I) else I(x)
 def __add__(self,o):
  o=I.co(o); return I.raw(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I.raw(-self.b,-self.a)
 def __sub__(self,o):return self+-I.co(o)
 def __rsub__(self,o):return I.co(o)+-self
 def __mul__(self,o):
  o=I.co(o);s=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b]
  return I.raw(min(s)//S,-((-max(s))//S))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=I.co(o)
  assert o.nz()
  f=[a*S//b for a in [self.a,self.b] for b in [o.a,o.b]]
  return I.raw(min(f),max(f)+1)
 def __rtruediv__(self,o):return I.co(o)/self
 def __pow__(self,n):
  t=I(1)
  for _ in range(n):t=t*self
  return t
 def nz(self):return self.a>0 or self.b<0
 def endpoints(self):return I.raw(self.a,self.a),I.raw(self.b,self.b)
 def include(self,o):return min(self.a,o.a),max(self.b,o.b)
def evalI(coeffs,x):
 t=I(0)
 for y in reversed(coeffs):t=y+x*t
 return t
a4=[1,-14,56,-84,42]; a5=[-1,20,-120,300,-330,132]
R4=lambda x:evalI(a4,x);R5=lambda x:evalI(a5,x)
from math import prod
def lam(a,d):return a/d
def checkchg(f,box):
 a,b=box.endpoints();u=f(a);v=f(b)
 assert (u.b<0<v.a) or (v.b<0<u.a)
def distinct(arr):
 assert all(x.b<y.a or y.b<x.a for x,y in combinations(arr,2))
source = (Path(__file__).resolve().parents[2] / "lean" / "RKCert" / "Research"
          / "ERK11SixTripleOneCrossGate.lean")
raw = source.read_text().split("def oneBoxes", 1)[1].split("def aMixed", 1)[0]
raw = "def oneBoxes" + raw
defs={}
for part in raw.split('def ')[1:]:
 name=part.split(' ')[0]; it=[]
 for line in part.splitlines()[1:]:
  zs=[I(int(a),int(b),10**int(n)) for n,a,b in re.findall(r'i(36|28) \((-?\d+)\) \((-?\d+)\)',line)]
  if zs: it.append(zs)
 defs[name]=it
cs=[]
for b,*extra in defs['oneBoxes']:
 d=1-b;e=1-b/2; q=[d,e]+extra
 l=R5(b)/R4(b); distinct(q)
 for x in extra:checkchg(lambda t:R4(b)*R5(t)+R5(b)*R4(t),x)
 for i in [2,3,4]: cs.append((q+[q[i]/2],i,5,0,1,l,True))
 for i in [1,2,3,4]: cs.append((q+[2*q[i]],5,i,0,1,l,True))
for u,*extra in defs['bothBoxes']:
 a,d=1+u,u;q=[a,d]+extra
 l=-R5(a)/R4(a); distinct(q)
 for x in extra:checkchg(lambda t:R4(a)*R5(t)-R5(a)*R4(t),x)
 cs.append((q+[a/2],0,5,1,5,l,False))
for x,*extra in defs['mixedBoxes']:
 a,d=2*x,4*x-1;q=[x,d]+extra
 l=-R5(x)/R4(x); distinct(q)
 for y in extra:checkchg(lambda t:R4(x)*R5(t)-R5(x)*R4(t),y)
 cs.append((q+[a],5,0,1,5,l,True))
cs+=[([1-x for x in q],di,ei,ai,ni,-lam,False) for q,ai,ni,di,ei,lam,flip in cs[:] if flip]
def pp(a,x):return x**3*(6*x*x-15*a*x+10*a*a)/30
def byindex(x,omit=-1):return [y for i,y in enumerate(x) if i!=omit]
def cross(q,ai,ni,di,ei,lam,L,z,x,cross):
 a,d,p=q[ai],q[di],q[5]
 H=[prod(q[i]-q[j] for j in range(5) if j!=i) for i in range(5)]
 d6=[(q[i]-p)*H[i] for i in range(5)]
 B=[-1/(13860*x*(x-1)*H[i]*R4(x)) for i,x in enumerate(q[:5])]
 B1=(7*lam+5)/(210*(lam+1))
 LF=[-a*a/2 if i==ai else x*x*(a-x)/a for i,x in enumerate(q)]
 RF=[-(1-d)**2/2 if i==di else (1-x)**2*(x-d)/(1-d) for i,x in enumerate(q)]
 K0=-B[cross]*d6[cross]*LF[cross]*RF[cross]
 ab=[(LF[i],-1/(B[i]*d6[i]*LF[i])) if i in L
     else (-K0/(B[i]*d6[i]*RF[i]),RF[i]/K0) for i in range(5)]
 K=-sum(v/H[i] for i,(v,w) in enumerate(ab))/sum(w/H[i] for i,(v,w) in enumerate(ab))
 u3=sum((v+w*K)*prod(p-y for y in byindex(q[:5],i))/H[i] for i,(v,w) in enumerate(ab))
 fl=LF[5];fr=RF[5]*K/K0;fx=u3-fl-fr
 mu=K/prod(p-y for y in q[:5])
 hs=[1/((y-1)*d6[i]*B[i]) for i,y in enumerate(q[:5])]
 h1=1/(B1*prod(1-y for y in q))
 gam=1/(K*(p-1))
 alpha=(gam**2*(fl*fr+fl*fx+fr*fx)*mu-sum(B[i]*hs[i]**2 for i in range(5))-B1*h1*h1)/(2*gam*mu)
 hb=lambda i:hs[i] if i<5 else alpha+gam*(fl*fl-u3*fl)
 ux=-1/(hb(ai)) if ai!=5 else -1/(alpha-gam*fl*fx)
 modes=[lambda i:ux*hb(i)] if ai!=5 else [lambda i: ux*hb(i),lambda i: I(-1) if i==5 else I(0)]
 ans=[]
 for h in modes:
  for z,x in [(z,x),(x,z)]:
   c=[ni,ai,z]
   vals=[]
   for i in c:
    ps=[q[j] for j in c if j!=i]
    u=-(pp(a,q[i])+h(i)*pp(a,a))/LF[i]
    vals.append(u*prod(q[x]-v for v in ps)/prod(q[i]-v for v in ps))
   ans.append(pp(a,q[x])+LF[x]*sum(vals)+h(x)*pp(a,a))
 return ans
n=0;t=0;m=None
for q,ai,ni,di,ei,lam,_ in cs:
 distinct([I(0),I(1)]+q)
 for (z,x),(u,y) in product(combinations([i for i in range(6) if i not in [ai,ni]],2),combinations([i for i in range(6) if i not in [di,ei]],2)):
  L=[ai,ai,ni,z,x];R=[di,di,ei,u,y]
  if any(L.count(i)+R.count(i)>2+(i==5) for i in range(6)):continue
  inter=(set(L)&set(R))-{5}
  if len(inter)!=1:continue
  n+=1
  arr=cross(q,ai,ni,di,ei,lam,L,z,x,next(iter(inter)))
  assert all(v.nz() for v in arr), (q,L,R,arr)
  t+=len(arr)
  inf=min(min(abs(v.a),abs(v.b)) for v in arr)
  m=inf if m is None else min(m,inf)
print('charts',len(cs),'assignments',n,'stage-7 signs',t,'minimum rational margin',m,'/',S)
assert (n,t)==(396,1044)
