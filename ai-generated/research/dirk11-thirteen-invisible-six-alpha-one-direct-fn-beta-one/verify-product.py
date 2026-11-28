#!/usr/bin/env python3
"""Exact common carrier projector and rank-two replay."""
from fractions import Fraction
from math import lcm,gcd,comb
from time import monotonic
from pathlib import Path
import argparse
from flint import fmpq,fmpq_poly,nmod_poly,nmod_mat
parser=argparse.ArgumentParser()
parser.add_argument("--p",type=int,default=0)
parser.add_argument("--check-bits",action="store_true")
parser.add_argument("--factor",type=Path)
parser.add_argument("--out",type=Path)

args=parser.parse_args()
p=args.p
baseMod=None
start_time=monotonic()
def log(*x): print(f'{monotonic()-start_time:8.2f}',*x,flush=True)
class Base:
    def to(self,x):
        if isinstance(x,PE):return x
        if isinstance(x,E):raise TypeError('upper algebra')
        if isinstance(x,(tuple,list)):
            return PE(POL([co(a) for a in x]))
        return PE(POL([co(x)]))
    def gen(self): return self.to([0,1])
base=Base()
def co(x):
    q=Fraction(x)
    if p:return q.numerator*pow(q.denominator,-1,p)%p
    return q.numerator if q.denominator==1 else fmpq(q.numerator,q.denominator)
POL=lambda c: nmod_poly(c,p) if p else fmpq_poly(c)
class PE:
    __slots__=('f',)
    def __init__(self,f):self.f=f%baseMod if baseMod is not None and f.degree()>=baseMod.degree() else f
    r=base
    def __eq__(self,x):
        if isinstance(x,E):return NotImplemented
        return self.f==base.to(x).f
    def __add__(self,x):
        if isinstance(x,E):return NotImplemented
        return PE(self.f+base.to(x).f)
    __radd__=__add__
    def __neg__(self):return PE(-self.f)
    def __sub__(self,x):
        if isinstance(x,E):return NotImplemented
        return PE(self.f-base.to(x).f)
    def __rsub__(self,x):
        if isinstance(x,E):return NotImplemented
        return base.to(x)-self
    def __mul__(self,x):
        if isinstance(x,E):return NotImplemented
        return PE(self.f*base.to(x).f)
    __rmul__=__mul__
    def __pow__(self,n):return PE(self.f**n)
    def __repr__(self):return str(self.f)
    def scale(self,z):return PE(self.f*co(z))
    def div_exact(self,f):
        q,r=divmod(self.f,f)
        assert r==0
        return PE(q)
class R:
    def __init__(self,low,mod,name):
        self.low=low; self.mod=tuple(low.to(c)for c in mod); self.n=len(mod)
        self.name=name
        self.z=low.to(0); self.o=low.to(1)
    def to(self,x):
        if isinstance(x,E) and x.r is self:return x
        return E(self,(self.low.to(x),)+(self.z,)*(self.n-1))
    def gen(self):return E(self,(self.z,self.o)+(self.z,)*(self.n-2))
class E:
    __slots__=('r','cs')
    def __init__(self,r,cs):self.r=r;self.cs=tuple(cs)
    def __eq__(self,x):
        try:return self.cs==self.r.to(x).cs
        except TypeError:return NotImplemented
    def __add__(self,x):
        try:z=self.r.to(x)
        except TypeError:return NotImplemented
        return E(self.r,[a+b for a,b in zip(self.cs,z.cs)])
    __radd__=__add__
    def __neg__(self):return E(self.r,[-x for x in self.cs])
    def __sub__(self,x):
        try:z=self.r.to(x)
        except TypeError:return NotImplemented
        return E(self.r,[a-b for a,b in zip(self.cs,z.cs)])
    def __rsub__(self,x):
        try:z=self.r.to(x)
        except TypeError:return NotImplemented
        return z-self
    def __mul__(self,x):
        if not isinstance(x,E) or x.r is not self.r:
            try:s=self.r.low.to(x)
            except TypeError:return NotImplemented
            return E(self.r,[a*s for a in self.cs])
        RR=self.r
        z=mul(self.cs,x.cs)
        return E(RR,rem(z,(*RR.mod,RR.o)))
    __rmul__=__mul__
    def __pow__(self,n):
        if n==0:return self.r.to(1)
        if n==1:return self
        z=self**(n//2)
        return z*z*self if n&1 else z*z
    def scale(self,q):return E(self.r,[a.scale(q) for a in self.cs])
    def div_exact(self,d):return E(self.r,[a.div_exact(d)for a in self.cs])
    def __repr__(self):return repr(self.cs)
def mul(f,g):
    r=f[0].r
    z=[r.to(0)]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a!=0:
            for j,b in enumerate(g):
                if b!=0:z[i+j]+=a*b
    return z
def rem(f,g):
    z=list(f)
    d=len(g)-1
    for i in range(len(z)-1,d-1,-1):
        k=z[i]
        if k!=0:
            for j,c in enumerate(g[:-1]):
                if c!=0:z[i-d+j]-=k*c
    return z[:d]+[f[0].r.to(0)]*max(0,d-len(z))
def cofact(f,x):
    a=x.r.to(f[-1])
    out=[a]
    for c in reversed(f[1:-1]):
        a=a*x+x.r.to(c);out.append(a)
    assert a*x+x.r.to(f[0])==0
    return list(reversed(out))
def ev(f,x):
    a=x.r.to(0)
    for c in reversed(f):a=a*x+x.r.to(c)
    return a
def prim(f):
    return [f[0].r.to(0),*(a.scale(Fraction(1,i+1)) for i,a in enumerate(f))]
def pplus(f,g):
    if len(f)<len(g):return pplus(g,f)
    return [*(a+b for a,b in zip(f,g)),*f[len(g):]]
def pscale(f,z): return [a*z for a in f]
def det(M):
    if len(M)==1:return M[0][0]
    if len(M)==2:return M[0][0]*M[1][1]-M[0][1]*M[1][0]
    return sum((-1)**i*c*det([[x for j,x in enumerate(row) if j!=i] for row in M[1:]])for i,c in enumerate(M[0]) if c!=0)
def cols(*C):return list(zip(*C))
def adjcol(M):
    return [(-1)**i*det([[M[j][k]for k in range(len(M))if k!=i]for j in range(1,len(M))])for i in range(len(M))]
def norm(x):
    y=x.r.gen()
    zs=[x]
    for _ in range(x.r.n-1):zs.append(zs[-1]*y)
    return det(cols(*(a.cs for a in zs)))
def flatten(x):
    if isinstance(x,PE):return [x.f]
    return sum([flatten(c)for c in x.cs],[])
def monic_f(f):
    if p:return f*f.leading_coefficient().__pow__(-1)
    return f/f.leading_coefficient()
def content(*xs):
    aa=sum([flatten(x)for x in xs],[])
    d=POL([])
    for a in aa:
        if a!=0:d=d.gcd(a)
        if d.degree()==0:break
    return monic_f(d)
def lose(name,*xs):
    d=content(*xs)
    if d.degree()>0:
        u=POL([1,-14,56,-84,42])*POL([0,-1,1])*POL([1,-16,72,-120,66])*POL([3,-32,108,-144,66])*POL([3,-64,604,-3096,9360,-17136,18648,-11088,2772])
        f=d
        while (q:=f.gcd(u)).degree()>0: f=f//q
        safe=d//f
        xs=tuple(x.div_exact(safe)for x in xs)
    if p: return xs
    fs=sum([flatten(x)for x in xs],[])
    l=lcm(*(int(f.denom())for f in fs))
    g=gcd(*(int(f.numer().content())*(l//int(f.denom()))for f in fs))
    if g: xs=tuple(x.scale(Fraction(l,g))for x in xs)
    log(name,'normalized coefficient degree',
        max(a.degree() for x in xs for a in flatten(x)),
        'guarded content degree',d.degree())
    return xs

if args.factor:
    fargs=list(map(int,args.factor.read_text().split()))
    if p:assert fargs[-1]%p
    baseMod=monic_f(POL(fargs))
    assert baseMod.degree()==len(fargs)-1
    def lose(name,*xs):return xs
v=base.gen()
J4=lambda y:42*y**4-84*y**3+56*y*y-14*y+1
J5=lambda y:(2*y-1)*(66*y**4-132*y**3+84*y*y-18*y+1)
L=132*J4(v)
Traw=pplus(pscale([base.to(c)for c in (-1,20,-120,300,-330,132)],J4(v)),pscale([base.to(c)for c in (1,-14,56,-84,42)],-J5(v)))
T4raw=cofact(Traw,v)
T4=[T4raw[i]*L**(3-i)for i in range(4)]+[base.to(1)]
K=R(base,T4[:-1],'fifth ordinary')
B=K.gen()
R3=cofact(T4,B)
c0,c1,c2,_=R3
Fn=[-c0*c1*c1,-12*c0*c1+12*c0*c2*c2-c1*c1*c2,-36*c0-4*c1*c2,12*c2]
L3=Fn[-1]
S=R(K,[Fn[i]*L3**(2-i)for i in range(3)],'Fn quadratic profile')
ss=S.gen()
B,L3,c0,c1,c2,L=(S.to(x)for x in (B,L3,c0,c1,c2,L))
V=S.to(v)*L
a,b=L-V,L-B
zero,one=S.to(0),S.to(1)
R3=[c0,c1,c2,one]
t1=c1*L3+6*ss
t0=6*c2*ss
m=lose('common m scale',ss*t1,t0*L3,t1*L3)

old_matrix=cols(*(rem([zero]*i+list(m),R3)for i in range(3)))
ma=adjcol(old_matrix)
den,chk1,chk2=rem(mul(m,ma),R3)
assert chk1==chk2==0
J4p=[L**4,-14*L**3,56*L**2,-84*L,42*one]
P0=[zero,*R3]
L0=prim(P0)[1:]
L1=prim([zero,*P0])[1:]
def fit(f):return rem(mul(ma,f),R3)
M=fit(J4p);W0=fit(L0)
H=[zero,*J4p]
def refl(f):
    return [(-1)**i*sum(comb(j,i)*f[j]*L**(j-i)for j in range(i,len(f))) for i in range(len(f))]
Rf=pscale(refl(R3),-one)
Mf=refl(M)
def monic_div(f,monic):
    x=list(f)
    n=len(monic)-1
    assert monic[-1]==1
    y=[x[0].r.to(0)]*max(0,len(x)-n)
    for i in range(len(x)-1,n-1,-1):
        y[i-n]=c=x[i]
        for j in range(n):x[i-n+j]-=c*monic[j]
    assert all(g==0 for g in x[:n])
    return y
P=[zero,*m]
IP=prim(P); I2P=prim(IP)
el=fit(IP[1:]); to=fit(I2P[1:])
u0,u1,u2=m
zp=u1*u2*c0
zq=3*u0*u2*c2-4*u0*u1-3*u2*u2*c0

class TPFactory:
    def to(self,c):return c if isinstance(c,TP) else TP([S.to(c)])
    def gen(self):return TP([zero,one])
T=TPFactory()
class TP:
    __slots__=('cs',)
    r=T
    def __init__(self,cs):
        cs=list(cs)
        while len(cs)>1 and cs[-1]==0:cs.pop()
        self.cs=tuple(cs)
    def __eq__(self,v):return self.cs==self.r.to(v).cs
    def __add__(self,v):
        v=self.r.to(v)
        return TP(pplus(self.cs,v.cs))
    __radd__=__add__
    def __neg__(self):return TP([-a for a in self.cs])
    def __sub__(self,v):return self+-self.r.to(v)
    def __rsub__(self,v):return self.r.to(v)+-self
    def __mul__(self,v):return TP(mul(self.cs,self.r.to(v).cs))
    __rmul__=__mul__
    def __pow__(self,n):
        assert n>=0
        r=self.r.to(1); a=self
        while n:
            if n&1:r=r*a
            a=a*a;n//=2
        return r
    def scale(self,c):return TP([x.scale(c)for x in self.cs])
    @property
    def degree(self):return -1 if self==0 else len(self.cs)-1

def et(a):return T.to(a)
def lift(f):return list(map(et,f))

# All entries below have a single horizontal clock scale. The new carrier
# variable X is the actual first middle ghost x.
X=T.gen()
v,b,pr,qr,nn=map(et,(V,B,zp,zq,den))
zeta=qr*v-pr
RR,WW,ELL,RHO,PP,P0T,J4T,MT=map(lift,(R3,W0,el,to,P,P0,J4p,M))
Z=[-pr,qr]
LL=pplus(mul(Z,ELL[:2]),pscale(RHO,-qr))
N=-(qr*LL[1]+pr*LL[2]+qr*LL[2]*X)
D=qr*WW[1]+pr*WW[2]+qr*WW[2]*X
A=LL[2]*D+N*WW[2]; assert A.degree<=0
QE=pplus(pscale(mul(Z,PP),D),pscale(P0T,N))
AdjX=(nn*qr.scale(Fraction(1,5))*D-A)*QE[4]*v*RR[0]+A*X*QE[1]
assert AdjX.degree<=2
log('compact AdjX constructed')
def crossDiv(f,g):
    # q² [f(z)g(Y)-g(z)f(Y)]/(Y-z)
    b=[f[0].r.to(0) for _ in range(3)]
    f=list(f)+[b[0]]*(4-len(f));g=list(g)+[b[0]]*(4-len(g))
    for i in range(4):
        for j in range(i+1,4):
            w=f[i]*g[j]-f[j]*g[i]
            for k in range(j-i): b[j-1-k]+=w*pr**(i+k)*qr**(2-i-k)
    return b
# Adj(A) exterior-square: if Mhat=Adj(A)m0, Dhat=Adj(A)d0, then
# Mhat ∧ Dhat / det A is A^T applied to the cyclic wedge of m0,d0.
Dt=pplus(lift(L1),pscale(lift(L0),-v))
dd0=rem([a-V*c for a,c in zip(L1,L0+[zero])],R3)
mm0=rem(J4p,R3)
Dfit=lift(fit(dd0))
w=[mm0[i]*dd0[j]-mm0[j]*dd0[i]for i,j in ((1,2),(2,0),(0,1))]
wfit=[sum(old_matrix[k][i]*w[k]for k in range(3))for i in range(3)]
rv=ev(RR,v);pv=ev(P0T,v);jv=ev(J4T,v)
e=[ [et(int(k==i))for k in range(3)]for i in range(3)]
ER=[crossDiv(a,RR)for a in e]
Delta=[et(0)]*3
for i,j,k,g in [(0,1,2,1),(0,2,1,-1),(1,2,0,1)]:
    c=pplus(pscale(crossDiv(e[i],e[j]),rv),
            pplus(pscale(ER[i],-v**j),pscale(ER[j],v**i)))
    Delta=pplus(Delta,pscale(c,et(wfit[k])*g))
crossM=crossDiv(MT,RR);crossD=crossDiv(Dfit,RR)
Qx0=pplus(pscale(Delta,ev(QE,v)),
          pscale(pplus(pscale(crossM,ev(Dt,v)),pscale(crossD,-jv)),zeta*v*D))
Qx=ev(Qx0,X); assert Qx.degree<=3
log('compact Qx constructed')

# Exact rank-two quadratic resultant with homogeneous padding. This is just
# the norm of a quadratic carrier remainder up to its leading pivots.
def form(g,d):
    return tuple(list(g.cs)+[zero]*(d+1-len(g.cs)))
a0,a1,a2=lose('AdjX',*form(AdjX,2))
q0,q1,q2,q3=lose('Qx',*form(Qx,3))
terms=[q0,q1,q2,q3]
PS=[2*one,-a1,a1*a1-2*a2*a0,3*a0*a1*a2-a1**3]
AP=[one,a2,a2*a2,a2**3];CP=[one,a0,a0*a0,a0**3]
ZQ=sum(terms[i]*terms[i]*AP[3-i]*CP[i]for i in range(4))+sum(
    terms[i]*terms[j]*CP[i]*AP[3-j]*PS[j-i]for j in range(4)for i in range(j))
res=ZQ
assert res!=0
while isinstance(res,E):
    res,=lose('relative projector',res)
    if args.check_bits and not p:
        log('bits',max(x.numer().height_bits()for x in flatten(res)))
    res=norm(res)
log('raw base degree',res.f.degree(), '' if p else res.f.numer().height_bits())

from flint import fmpz_poly
from heapq import heappush, heappop
import itertools
dst=Path(__file__).resolve().parent
raw=res.f.numer()
assert not p and res.f.denom()==1
D={1:420,2:96,12:28,18:8,19:48,21:60,72:12,279:4,472:12,918:4}
fs={k:fmpz_poly(list(map(int,(dst/'factors'/f'sf{k}.txt').read_text().split())))for k in D}
assert {e:f.degree()for e,f in fs.items()}==D
assert all(f.content()==1 and f.leading_coefficient()>0 for f in fs.values())
assert sum(e*f.degree()for e,f in fs.items())==raw.degree()
rc=raw.content(); assert rc!=0
raw=raw//(rc if raw.leading_coefficient()>0 else -rc)
pq=[];ix=itertools.count()
for e,g in fs.items():
    h=g**e
    heappush(pq,(h.degree(),next(ix),h))
    log("raised",e,h.degree(),h.height_bits())
while len(pq)>1:
    _,_,a=heappop(pq); _,_,b=heappop(pq)
    h=a*b;heappush(pq,(h.degree(),next(ix),h)); log("merged",h.degree(),h.height_bits())
assert raw==pq[0][2]
log("EXACT PRODUCT equality",raw.degree(),raw.height_bits())
safe=fmpz_poly([1,-14,56,-84,42])*fmpz_poly([0,-1,1])*fmpz_poly([1,-16,72,-120,66])*fmpz_poly([3,-32,108,-144,66])*fmpz_poly([3,-64,604,-3096,9360,-17136,18648,-11088,2772])
dec=[]
for e,f in sorted(fs.items()):
    f=f//f.gcd(safe)
    assert f.gcd(f.derivative()).degree()==0
    print('level',e,'deg',f.degree(),'bits',f.height_bits(),flush=True)
    for g,m in f.factor()[1]:
        assert m==1
        dec.append((e,g)); log('exact irreducible residual factor',e,g.degree(),g[0])
dec=sorted(dec,key=lambda eg:(eg[1].degree(),int(eg[1][0])))
assert [g.degree() for e,g in dec]==[12,12,24,36,48,60,60,60,108,252]
assert sum(g.degree()for e,g in dec)==672
assert len({(g.degree(),int(g[0]))for e,g in dec})==10
out=args.out
assert out is not None
out.mkdir(exist_ok=True)
for i,(e,g)in enumerate(dec):
    (out/f'{i:02d}.txt').write_text(' '.join(map(str,g.coeffs()))+'\n')
