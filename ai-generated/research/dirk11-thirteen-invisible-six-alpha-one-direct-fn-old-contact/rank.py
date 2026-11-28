#!/usr/bin/env python3
from fractions import Fraction
from time import monotonic
from flint import nmod_poly,nmod_mat
from argparse import ArgumentParser
p0=ArgumentParser()
p0.add_argument('--prime',type=int,choices=(103,),default=103)
p=p0.parse_args().prime
baseMod=None
start_time=monotonic()
def log(*x): print(f'{monotonic()-start_time:8.2f}',*x,flush=True)
class Base:
    def to(self,x):
        if isinstance(x,PE):return x
        if isinstance(x,(tuple,list)):
            return PE(POL([co(a) for a in x]))
        return PE(POL([co(x)]))
    def gen(self): return self.to([0,1])
base=Base()
def co(x):
    q=Fraction(x)
    return q.numerator*pow(q.denominator,-1,p)%p
POL=lambda c:nmod_poly(c,p)
class PE:
    __slots__=('f',)
    def __init__(self,f):self.f=f%baseMod if baseMod is not None and f.degree()>=baseMod.degree() else f
    r=base
    def __eq__(self,x):
        return self.f==base.to(x).f
    def __add__(self,x):
        return PE(self.f+base.to(x).f)
    __radd__=__add__
    def __neg__(self):return PE(-self.f)
    def __sub__(self,x):
        return PE(self.f-base.to(x).f)
    def __rsub__(self,x):
        return base.to(x)-self
    def __mul__(self,x):
        return PE(self.f*base.to(x).f)
    __rmul__=__mul__
    def __pow__(self,n):return PE(self.f**n)
    def __repr__(self):return str(self.f)
    def scale(self,z):return PE(self.f*co(z))
    def div_exact(self,f):
        q,r=divmod(self.f,f)
        assert r==0
        return PE(q)
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
from clock import gatecontents,W,c1,c2,c0,V as SV,B as SB0,J4
import sympy as sy
content,G,ls,fs=gatecontents('old z collision',W)
assert sorted((q.degree(),e)for q,e in fs)==[(4,7),(48,1)]
assert next(f for f,e in fs if f.degree()==4).monic()==sy.Poly(J4(SV),SV).monic()
assert sy.Poly(content,SV).monic()==sy.Poly(J4(SV)**3,SV).monic()
f=next(f for f,e in fs if f.degree()==48).monic()
Dg=48
baseMod=POL([co(Fraction(f.nth(i))) for i in range(Dg+1)])
assert baseMod.degree()==Dg
assert baseMod.gcd(baseMod.derivative()).degree()==0
def inv(a):
    dd,ai,qq=a.f.xgcd(baseMod)
    assert dd.degree()==0,('not a unit',dd.degree())
    u=PE(ai*dd[0]**(-1))
    assert a*u==1
    return u
def fullvec(f):
    return [int(f.f[i])for i in range(Dg)]
S=base
J4co=(1,-14,56,-84,42)
J5co=(-1,20,-120,300,-330,132)
V=base.gen()
L1coeff=ls[-2];assert L1coeff.degree()==1
def liftV(a):
    q=sy.Poly(a,SV)
    return ev([base.to(Fraction(q.nth(i)))for i in range(q.degree()+1)],V)
B=-liftV(L1coeff.nth(0))*inv(liftV(L1coeff.nth(1)))
lam=-ev([base.to(i)for i in J5co],V)*inv(ev([base.to(i)for i in J4co],V))
T5=[(base.to(J5co[i])+lam*J4co[i]).scale(Fraction(1,132))for i in range(5)]+[base.to(1)]
R3=cofact(cofact(T5,V),B)
c0,c1,c2,_=R3
rr=-(5400*c0-500*c1*c2)*inv(-2000*c1+625*c2*c2)
ss=(rr*rr).scale(Fraction(5,24))
assert 5*rr*rr-5*c2*rr+4*c1==0
assert 100*rr**3-75*c2*rr*rr+216*c0==0
assert ev(R3,rr.scale(Fraction(-5,6)))==0
assert rr*(c1+6*ss)==6*c2*ss
one,zero=S.to(1),S.to(0)
m=(ss,rr,one)
for i,g in enumerate((c0,c2,V,1-V,B,1-B,V-B,ev(R3,V),ev(R3,B),
                     3*c2*ss-4*rr*ss-3*c0,ss,rr,c2*ss-c0,c1+6*ss)):
    try:inv(g)
    except AssertionError as e:raise AssertionError(('additional pivot',i,e)) from e
log('all residue collision and geometry pivots live')
A0=cols(*(rem([zero]*i+list(m),R3)for i in range(3)))
mAdj=tuple(adjcol(A0))
n,ch1,ch2=rem(mul(m,mAdj),R3)
assert ch1==ch2==0
def fit(f):return rem(mul(mAdj,f),R3)
j=[S.to(i)for i in J4co]
M=fit(j)
P=[zero,*m]; Pi=prim(P);Pii=prim(Pi)
P0=[zero,*R3]; I0=prim(P0); L0=I0[1:]; L1=prim([zero,*P0])[1:]
W=fit(L0)
el=fit(Pi[1:]); rho=fit(Pii[1:])
u0,u1,u2=m
zp=u1*u2*c0
zq=3*u0*u2*c2-4*u0*u1-3*u2*u2*c0
def hom(f,x,d):return sum(f[i]*x**i*d**(len(f)-1-i)for i in range(len(f)))
assert el[2]==0 and hom(el,zp,zq)==0 and hom(rho,zp,zq)==0 and hom(W,zp,zq)==0
log("clock tower and actual fit built")
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
    def __add__(self,v):return TP(pplus(self.cs,self.r.to(v).cs))
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
    def pad(self,n):return list(self.cs)+[zero]*max(0,n-len(self.cs))
et=T.to
def lift(f):return list(map(et,f))
Evar=T.gen()
z,o=et(0),et(1)
v,b,pr,qr,nn=map(et,(V,B,zp,zq,n))
zeta=qr*v-pr
zpold=[-pr,qr]
RR,WW,ELL,RRHO,PP,P0T,J4T,MT,L0T,L1T=map(lift,(R3,W,el,rho,P,P0,j,M,L0,L1))
ELL=ELL[:2]
Q4=pplus(mul(zpold,PP),pscale(P0T,Evar))
IQ4=prim(Q4)
ML=pplus(pplus(mul(zpold,ELL),pscale(RRHO,-qr)),pscale(WW,Evar))
def divmonic(f,g):
    work=list(f)
    d=len(g)-1
    out=[f[0].r.to(0)]*(len(f)-d)
    assert g[-1]==1
    for i in range(len(f)-1,d-1,-1):
        a=work[i];out[i-d]=a
        for k in range(d):work[i-d+k]-=a*g[k]
    assert all(a==0 for a in work[:d])
    return out
AR=divmonic(pplus(mul(ML,Q4),pscale(mul(zpold,IQ4),-nn)),P0T)
Adj=ev(AR,v)
assert Adj.degree<=2
QR=ev(Q4,v)
xnum=-(qr*ML[1]+pr*ML[2]);xden=qr*ML[2]
log("new Adj",Adj.degree)

rv=ev(RR,v);pv=ev(P0T,v);jv=ev(J4T,v)
SM=pplus(pscale(MT,rv),pscale(RR,-ev(MT,v)))
Dc=pplus(L1T,pscale(L0T,-v))
DT=lift(fit([k-v0*V for k,v0 in zip(L1,L0+[zero])]))
SD=pplus(pscale(DT,rv),pscale(RR,-ev(DT,v)))
Sg=pplus(pscale(SM,QR),pscale(RR,nn*zeta*v*jv))
Sgz=hom(Sg,pr,qr)
# Every crossed fit below has four coefficients, so all z reads
# use the same homogeneous exponent 3, including dropped leaders.
def cross(a,b):return pplus(pscale(b,hom(a,pr,qr)),pscale(a,-hom(b,pr,qr)))
def divz2(f):
    assert len(f)==4
    return [qr*qr*f[1]+pr*qr*f[2]+pr*pr*f[3],qr*qr*f[2]+pr*qr*f[3],qr*qr*f[3]]
QS=pplus(pscale(cross(SM,SD),QR),
         pplus(pscale(cross(SM,RR),nn*zeta*v*ev(Dc,v)),pscale(cross(SD,RR),-nn*zeta*v*jv)))
QGate=hom(divz2(QS),xnum,xden)
assert QGate.degree<=3
log("quintic after affine middle",QGate.degree)

Dden=nn*zeta*pv
Dnum=zeta*nn*ev(prim(P0T),v)-ev(WW,v)*QR
CM=cross(MT+[z],RR)
Fhat=[qr*WW[1]+pr*WW[2],qr*WW[2]]
Mid=pplus(pscale(mul(Fhat,[-v*Dden-Dnum,Dden]),qr*Sgz),
          pscale(divz2(CM),-Dnum*Dnum))
Mgate=hom(Mid,xnum,xden)
assert Mgate.degree<=4
log("commutator after affine middle",Mgate.degree)

# Fixed-degree Macaulay map over the entire monic degree-24 algebra.
D=5
vps=[V**i for i in range(Dg)]
columns=[]
for f,e in ((Adj,2),(QGate,3),(Mgate,4)):
    assert f.degree<=e
    for u in vps:
        coe=sum([fullvec(a*u)for a in f.cs],[])
        for i in range(D-e+1):
            c=[0]*(Dg*i)+coe
            columns.append(c+[0]*(Dg*(D+1)-len(c)))
rank=nmod_mat(list(map(list,zip(*columns))),p).rank()
assert rank==(D+1)*Dg
print(f'Entire monic degree-{Dg} algebra, p={p}: rank {rank}/{(D+1)*Dg} at cap 5.')
