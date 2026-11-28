#!/usr/bin/env python3
"""Exact pure late-kernel slope-minus-one clock projection."""
from fractions import Fraction
from math import lcm,gcd,comb
from time import monotonic
from pathlib import Path
import argparse
from flint import fmpq,fmpq_poly,nmod_poly,nmod_mat
parser=argparse.ArgumentParser()
# Fully symbolic carrier E at a fixed residue V; not a tableau reduction.
p=103
baseMod=nmod_poly([-2,1],p)
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
ma=lose('old common adjugate',*adjcol(old_matrix))
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
# Common clock and direct-Fn monic algebra are already constructed.
# All coefficient arrays below use the same scaled reverse variable.
EE=T.gen()
zz,oo=et(0),et(1)
v,b,Ls,pr,qr,nn=map(et,(V,B,L,zp,zq,den))
zeta=qr*v-pr
RR,WW,ELL,RRHO,PP,P0T,J4T,MT=map(lift,(R3,W0,el,to,P,P0,J4p,M))
ELL=ELL[:2]
Z=[-pr,qr]
Q4=pplus(mul(Z,PP),pscale(P0T,EE))
IQ4=prim(Q4)
ML=pplus(pplus(mul(Z,ELL),pscale(RRHO,-qr)),pscale(WW,EE))
xn=-(qr*ML[1]+pr*ML[2]);xd=qr*ML[2]
etahat=qr*(nn*qr.scale(Fraction(1,5))-ML[2])*Q4[4]
Adj=etahat*v*RR[0]+xn*Q4[1]
assert Adj.degree<=2
Q_V=ev(Q4,v)
rv=ev(RR,v);pv=ev(P0T,v);jv=ev(J4T,v)
SM=pplus(pscale(MT,rv),pscale(RR,-ev(MT,v)))
U=pplus(pscale(SM,Q_V),pscale(RR,nn*zeta*v*jv))
H=[zz,*J4T]
P5=mul([-v,oo],P0T)
# The actual B transfer signal is zero exactly when this polynomial vanishes there.
Dpoly=pplus(pscale(mul(Z,H),nn*rv*Q_V),pscale(mul(Q4,U),-oo))
Bzero=ev(monic_div(Dpoly,P5),b)
assert Bzero.degree<=2
Fint=prim(mul([Ls,-oo],U))
Jb=ev(Fint,Ls)-ev(Fint,b)
fb=Ls-b; ub=ev(U,b)
Dbgap=Jb*xd-fb*ub*(b*xd-xn)
assert Dbgap.degree<=2
# Exact native identities for Adj and the B pin are certified separately.

def h(f,A,D):return sum(f[i]*A**i*D**(len(f)-1-i)for i in range(len(f)))
def cross3(f,g):
    return pplus(pscale(g,h(f,pr,qr)),pscale(f,-h(g,pr,qr)))
Sz=h(U,pr,qr)
Dt=pplus(lift(L1),pscale(lift(L0),-v))
Dm=lift(fit([a-V*c for a,c in zip(L1,L0+[zero])]))
SD=pplus(pscale(Dm,rv),pscale(RR,-ev(Dm,v)))
Qp=pplus(pscale(cross3(SM,SD),Q_V),
   pplus(pscale(cross3(SM,RR),nn*zeta*v*ev(Dt,v)),
         pscale(cross3(SD,RR),-nn*zeta*v*jv)))
assert len(Qp)==4 and all(g.degree<=1 for g in Qp)
def divz2(f):
   assert len(f)==4
   return [qr**2*f[1]+pr*qr*f[2]+pr**2*f[3],qr**2*f[2]+pr*qr*f[3],qr**2*f[3]]
DD=divz2(Qp)
Qpin=h(DD,xn,xd)
assert Qpin.degree<=3
# Literal first-middle commutator after d_x=0.
Dden=nn*zeta*pv
Dnum=nn*zeta*ev(prim(P0T),v)-ev(WW,v)*Q_V
CM=cross3(MT+[zz],RR)
W1=[qr*WW[1]+pr*WW[2],qr*WW[2]]
M0=pplus(pscale(mul(W1,[-v*Dden-Dnum,Dden]),qr*Sz),pscale(divz2(CM),-Dnum**2))
Mid=h(M0,xn,xd)
assert Mid.degree<=4
# L5 is the true Q5 divided by (Y−z)(Y−x). All x/z differences
# and carrier clocks used here are live by the earlier actual packets.
C=[xd*DD[1]+xn*DD[2],xd*DD[2]]
Cden=xd*qr**2*nn*rv*Sz
assert all(g.degree<=2 for g in C) and Cden.degree<=2
# Ordinary fifth diagonal versus the exact kernel transfer.
A,Bb=ML[2],ML[2]+nn*qr
EtaN=(nn*qr.scale(Fraction(1,5))-A)*Q4[4]
EtaD=nn*qr**2
bx=b*xd-xn
OmegaN=bx*Bzero;OmegaD=xd*qr*ub
NuN=EtaN*OmegaD-qr*Bb*OmegaN
NuD=EtaD*OmegaD
assert NuN.degree<=4 and NuD.degree<=2
Bg=Jb*xd*NuN-fb*ub*bx*(NuN+EtaD*OmegaN)
assert Bg.degree<=6
Ynum=xn*NuD*Cden+nn*qr**2*NuN*C[0]
Yden=qr*A*NuD*Cden-nn*qr**2*NuN*C[1]
assert Ynum.degree<=6 and Yden.degree<=6
# The direct y commutator. Reconstruct its two-root interpolant
# without selecting any additional coefficient extension.
DD4=mul([-v,oo],RR)
Sx=h(U,xn,xd); Dz=h(DD4,pr,qr); Dx=h(DD4,xn,xd)
dXZ=qr*xn-pr*xd
Cd=dXZ*Sz*Sx
Tint=pplus(pscale([xn,-xd],Dz*Sx),pscale(Z,Dx*Sz))
CN=pplus(pscale(DD4,Cd),pscale(mul(U,Tint),-oo))
assert len(CN)==5 and all(g.degree<=6 for g in CN)
CQz=[qr**3*CN[1]+pr*qr**2*CN[2]+pr**2*qr*CN[3]+pr**3*CN[4],
     qr**3*CN[2]+pr*qr**2*CN[3]+pr**2*qr*CN[4],qr**3*CN[3]+pr*qr**2*CN[4],qr**3*CN[4]]
CQ=[xd**2*CQz[1]+xn*xd*CQz[2]+xn**2*CQz[3],
    xd**2*CQz[2]+xn*xd*CQz[3],xd**2*CQz[3]]
assert all(g.degree<=8 for g in CQ)
LatePoly=pplus(pscale(mul([-b*fb*ub-Jb,fb*ub],C),fb*nn*rv*Q_V*ev(J4T,b)*qr**3*xd**2*Cd),
               pscale(CQ,-Jb**2*Cden))
assert len(LatePoly)==3 and all(g.degree<=12 for g in LatePoly)
Late=h(LatePoly,Ynum,Yden)
assert Late.degree<=24
print('carrier caps actually attained',Adj.degree,Qpin.degree,Mid.degree,Bg.degree,
      (Ynum.degree,Yden.degree),[a.degree for a in LatePoly],Late.degree,flush=True)
