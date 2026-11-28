#!/usr/bin/env python3
"""Exact characteristic-zero midpoint field fibre, with python-flint."""
from fractions import Fraction as Q
from pathlib import Path
import json,runpy,flint as fl,time
P=Path(__file__).parent
M=runpy.run_path(str(P/'verify.py'))
src=json.loads((P/'projection.json').read_text())
M0=src['bases'][0]
n=max(i for i,j,k,c in M0)
vv=[0]*(n+1)
for i,j,k,c in M0:vv[i]=c
class QQKey:
    def __init__(self,M):
        self.m=fl.fmpq_poly(M)
        self.one=fl.fmpq_poly([1])
    def __call__(self,x):
        if isinstance(x,QQV) and x.F is self:return x
        p=x if isinstance(x,list) else [x]
        pp=[fl.fmpq(q.numerator,q.denominator) if isinstance(q,Q) else int(q) for q in p]
        return QQV(self,fl.fmpq_poly(pp)%self.m)
class QQV:
    def __init__(self,F,u):self.F=F;self.u=u
    def __bool__(self):return bool(self.u)
    def __eq__(self,x):return self.u==self.F(x).u
    def __add__(self,x):return QQV(self.F,self.u+self.F(x).u)
    __radd__=__add__
    def __mul__(self,x):return QQV(self.F,(self.u*self.F(x).u)%self.F.m)
    __rmul__=__mul__
    def __neg__(self):return QQV(self.F,-self.u)
    def __sub__(self,x):return self+-self.F(x)
    def __rsub__(self,x):return self.F(x)+-self
    def __pow__(self,x):
        if x<0:return self.inv()**(-x)
        u=self.F(1);v=self
        while x:
            if x&1:u*=v
            x//=2
            if x:v*=v
        return u
    def inv(self):
        d,s,t=self.u.xgcd(self.F.m);assert d==self.F.one
        return QQV(self.F,s%self.F.m)
    def __truediv__(self,o):return self*self.F(o).inv()
    def __rtruediv__(self,o):return self.F(o)*self.inv()
def form(F,x,y,rs,var):
    a=[F(1)]*(max(i for i,j,k,c in rs)+1)
    b=[F(1)]*(max(j for i,j,k,c in rs)+1)
    for i in range(1,len(a)):a[i]=a[i-1]*x
    if var!=1:
        for i in range(1,len(b)):b[i]=b[i-1]*y
    V=[F(0)]*(max(r[var] for r in rs)+1)
    for row in rs:
        i,j,k,c=row
        V[row[var]]+=a[i]*b[j]*c
    return M['trim'](V)
st=time.monotonic()
F=QQKey(vv);x=F([0,1]);o=F(1)
E=form(F,x,o,src['G3'],1);H=form(F,x,o,src['H'],1)
print('formed y input',time.monotonic()-st,flush=True)
Y=M['gcd'](E,H);print('ygcd',len(Y)-1,time.monotonic()-st,flush=True)
assert len(Y)==2
y=-Y[0]
E2=form(F,x,y,src['E2'],2);E3=form(F,x,y,src['E3'],2)
print('formed t input',time.monotonic()-st,flush=True)
T=M['gcd'](E2,E3);print('tgcd',len(T)-1,time.monotonic()-st,flush=True)
assert len(T)==2
t=-T[0]
def dump(w):return [[int(z.numerator),int(z.denominator)] for z in w.u]
leaf,g=M['instance'](F,F(Q(1,2)),x,y,t)
assert leaf=='fifth' and len(g)==4
result=dict(x=vv,y=dump(y),t=dump(t),f=[dump(f) for f in g])
dest=P/'field.json'
if dest.exists():assert json.loads(dest.read_text())==result
else:dest.write_text(json.dumps(result,separators=(',',':'))+'\\n')
print('unique rational y,t; exact surviving fifth cubic in the degree-36 midpoint field',flush=True)
