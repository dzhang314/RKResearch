#!/usr/bin/env python3
"""Alpha=1 tau live cubic true F7 projection."""
from fractions import Fraction
from math import lcm,gcd,comb
from time import monotonic
from pathlib import Path
import argparse
from flint import fmpq,fmpq_poly,nmod_poly,nmod_mat
parser=argparse.ArgumentParser()
parser.add_argument('--exact',type=int,choices=(1,2))
args=parser.parse_args()
p=0 if args.exact else 103
baseMod=None if args.exact else nmod_poly([-2,1],p)
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
    # No scalar content is removed in the nonzero proof.
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
M=fit(J4p);W0=fit(L0);Q0=fit(L1)
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
d4=monic_div(pplus(mul(L0,M),pscale(mul(W0,J4p),-one)),R3)
d5=monic_div(pplus(mul(L1,M),pscale(mul(Q0,J4p),-one)),R3)
P=[zero,*m]
IP=prim(P); I2P=prim(IP)
el=fit(IP[1:]); to=fit(I2P[1:])
u0,u1,u2=m
zp=u1*u2*c0
zq=3*u0*u2*c2-4*u0*u1-3*u2*u2*c0

# Polynomials in the carrier t. Distinguish them from all clock polynomials
# and use full-size coefficient arc even when the induced t degree drops.
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

def listT(f):return list(map(T.to,f))
def et(a):return T.to(a)
ts=T.gen()
o,z=et(1),et(0)
vr,br,ls,ar,bs=map(et,(V,B,L,a,b))
Mt,Rt,L0t,L1t,Wt,Qt,J4t,Ht=map(listT,(M,R3,L0,L1,W0,Q0,J4p,H))
UR=pplus(Mt,pscale(Rt,ts))
def rev(f):
    return [(-1)**i*sum(comb(j,i)*f[j]*ls**(j-i) for j in range(i,len(f))) for i in range(len(f))]
UF=rev(UR)
U_V=ev(UR,vr)
cv=ev(listT(d4),vr)+ts*ev(L0t,vr)
jv=ev(J4t,vr)
hv=vr*jv
qr,pr=et(zq),et(zp)
Adj=(pr-vr*qr)*((et(ev(el,V))*hv-et(ev(IP,V))*U_V)*U_V+
                 cv*(et(ev(P,V))*U_V-et(den)*hv)) - qr*(et(ev(I2P,V))*U_V-et(ev(to,V))*hv)*U_V
ff=prim(mul([z,-bs,o],UF))
Kf=pplus(pscale(ff,ev(Ht,bs)),pscale(Ht,-ev(ff,bs)))
KbDiv=cofact(cofact(rev(Kf),ls),br)
N=mul([-vr,o],Mt)
Dr=mul([-vr,o],Rt)
E6=det(cols(UR,N,rem([z,*N],Dr),rem(mul([-pr,qr],KbDiv),Dr)))
assert Adj.degree<=2 and E6.degree<=2
gates={'E6':E6,'Adj':Adj}

d5v=ev(listT(d5),vr)+ts*ev(L1t,vr)
B5=pplus(pscale(pplus(Qt,pscale(Wt,-vr)),jv),
         pscale(Rt,d5v-vr*cv))
def hom(f,x,d):return sum(f[i]*x**i*d**(len(f)-1-i)for i in range(len(f)))
Uh=hom(UR,pr,qr)
Q5=pplus(pscale(B5,Uh),pscale(UR,-hom(B5,pr,qr)))
assert all(q.degree<=1 for q in Q5)
J=prim([z,*UF])
B2=ev(J,bs)**2*det(cols(Q5,rem([z,*Q5],Dr),UR,N))
assert B2.degree<=5
# Independently recompute the reflected primitive, with the reverse
# variable measured from the correct endpoint.
RJ=prim(mul([ls,-o],UR))
assert rev(J)==pplus([ev(RJ,ls)],pscale(RJ,-o))
assert rev(Ht)==mul([ls,-o],J4t)
Jdiv=cofact(rev(J),ls)
DR2=mul([-br,o],Dr)
M2=mul(mul([-vr,o],[-br,o]),Mt)
C0=rem(mul([-pr,qr],Jdiv),DR2)
C1=rem([z,*C0],DR2)
# These five columns live in degree-at-most-four coefficients.
WW=[UR+[z],[z,*UR],M2,rem([z,*M2],DR2)]
g1,g0=(det(cols(*WW,f))for f in (C0,C1))
assert g1.degree<=3 and g0.degree<=3
q0,q1,q2,q3=Q5
dd=[qr*qr*q1+pr*qr*q2+pr*pr*q3,qr*qr*q2+pr*qr*q3,qr*qr*q3]
B1=hom(dd,g0,g1)
assert B1.degree<=7
gates.update(B1=B1,B2=B2,UatV=U_V,UatB=ev(UR,br),UatO=ev(UR,ls),UatZ=Uh)



def res_quad(q,g):
    """Fixed-degree universal resultant of c+b*t+a*t^2 and g."""
    c,b,a=q;r=c.r;k=len(g)-1
    ps=[r.to(2),-b]
    for i in range(2,k+1):ps.append(-b*ps[-1]-a*c*ps[-2])
    ap=[a**i for i in range(k+1)]
    cp=[c**i for i in range(k+1)]
    return sum(g[i]*g[i]*ap[k-i]*cp[i] for i in range(k+1))+sum(
        g[i]*g[j]*cp[i]*ap[k-j]*ps[j-i]
        for j in range(k+1) for i in range(j))

def fixed(t,n):
    assert t.degree<=n
    return list(t.cs)+[zero]*(n+1-len(t.cs))
noms={1:(B1,7),2:(B2,5)}
for i in ([args.exact] if args.exact else (1,2)):
    eq,deg=noms[i]
    A=res_quad(fixed(Adj,2),fixed(eq,deg))
    while isinstance(A,E):A=norm(A)
    assert A.f!=0
    if p:
        assert A.f.degree()==0
        print('beta',i,'nominal carrier degrees',2,deg,
              'nonzero norm at V=2 mod 103:',int(A.f[0]),flush=True)
    else:
        log('exact rational norm degree',A.f.degree())
