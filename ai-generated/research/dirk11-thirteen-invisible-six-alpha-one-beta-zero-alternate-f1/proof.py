from fractions import Fraction
from math import lcm,gcd,comb
from time import monotonic
from pathlib import Path
import argparse
from flint import fmpq,fmpq_poly,nmod_poly,nmod_mat
import sympy as sp
parser=argparse.ArgumentParser()
parser.add_argument("--p",type=int)
parser.add_argument("--residue-index",type=int,default=0)
args=parser.parse_args()
p=args.p or 103
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

XV, XB, Y=sp.symbols('V B Y')
def J4(x): return 42*x**4-84*x**3+56*x**2-14*x+1
def J5(x): return 132*x**5-330*x**4+300*x**3-120*x**2+20*x-1
T=sp.Poly(J5(Y)*J4(XV)-J5(XV)*J4(Y),Y).exquo(sp.Poly(Y-XV,Y))
D=T.LC()
FB=sp.Poly(T.as_expr().subs(Y,XB),XB)
C2=T.nth(3)+XB*D; C1=T.nth(2)+XB*C2; C0=T.nth(1)+XB*C1
A,S0,S1,S2=sp.symbols("A S0 S1 S2")
p3=25*A**3+25*S2*A**2-192*S0
p2=15*S2*A**2-8*S1*A-48*S0
RH=3600*S0**2+3720*S0*S1*S2-2205*S0*S2**3+128*S1**3+240*S1**2*S2**2
assert sp.expand(sp.resultant(p3,p2,A)+19200*S0*RH)==0
lc=sp.Poly(RH,S0,S1,S2)
HH=sum(z*C0**ex[0]*C1**ex[1]*C2**ex[2]*D**(lc.total_degree()-sum(ex))for ex,z in lc.terms())
pc_content,G=sp.Poly(HH,XB).prem(FB).primitive()
assert sp.Poly(pc_content,XV).monic()==sp.Poly(J4(XV)**3,XV).monic()
fs=sp.factor_list(sp.Poly(sp.resultant(FB,G,XB),XV))[1]
assert sorted((f.degree(),int(f.nth(0)),e)for f,e in fs)==[(4,1,7),(48,-14638292540815408663567,1)]
assert next(f for f,e in fs if f.degree()==4).monic()==sp.Poly(J4(XV),XV).monic()
f=next(f for f,e in fs if f.degree()==48);dd=48
gs=sp.Poly(sp.subresultants(FB,G,XB)[-2],XB);assert gs.degree()==1
h0,h1=(sp.Poly(gs.nth(i),XV,domain=sp.QQ)for i in range(2))
fq=sp.Poly(f,XV,domain=sp.QQ)
assert sp.gcd(h1,fq).degree()==0
u=sp.invert(h1,fq)
assert (u*h1).rem(fq)==sp.Poly(1,XV,domain=sp.QQ)
bm=(-h0*u).rem(fq)
# Check the entire exact gcd in the ordinary B variable, not merely a
# syntactically linear subresultant before its specialization.
def exact(P):
    return fmpq_poly([fmpq(int(x.p),int(x.q)) for x in reversed(sp.Poly(P,XV,domain=sp.QQ).all_coeffs())])
Fexact=exact(fq)
Fexact=Fexact/Fexact.leading_coefficient()
def Bcoeff(P):
    q=[exact(P.nth(i))%Fexact for i in range(P.degree()+1)]
    while q and q[-1]==0:q.pop()
    return q
def exact_inverse(h):
    g,x,_=h.xgcd(Fexact)
    assert g==1 and h*x%Fexact==1
    return x
def grem(a,b):
    v=list(a); i=exact_inverse(b[-1])
    for k in range(len(a)-1,len(b)-2,-1):
        c=v[k]*i%Fexact
        for j in range(len(b)):
            l=k+j-len(b)+1
            v[l]=(v[l]-c*b[j])%Fexact
    assert not any(v[len(b)-1:])
    v=v[:len(b)-1]
    while v and v[-1]==0:v.pop()
    return v
a0,b0=Bcoeff(FB),Bcoeff(G)
while b0:a0,b0=b0,grem(a0,b0)
assert len(a0)==2 and a0[0]*exact_inverse(a0[1])%Fexact==(-exact(bm))%Fexact
bex=exact(bm)%Fexact
vex=fmpq_poly([0,1])
assert bex!=vex and bex!=0 and bex!=1
def at_base(v,x):
    p=exact(v)
    out=fmpq_poly([])
    for b in reversed(p.coeffs()):out=(out*x+b)%Fexact
    return out
assert at_base(f,bex)==0
assert at_base(h0,bex)+at_base(h1,bex)*vex%Fexact==0
assert at_base(h1,bex)!=0 and at_base(J4(XV),bex)!=0
log("exact physical V/B transposition on the same degree-48 field")
log('exact ordinary V degree',dd,'constant',f.nth(0),'exact B gcd linear and pivot unit')
def vB(poly):
    bq=exact(bm)%Fexact
    ans=fmpq_poly([])
    for v in reversed(Bcoeff(poly)):ans=(ans*bq+v)%Fexact
    return ans
qq=exact(sp.Poly(D,XV,domain=sp.QQ))%Fexact
qinv=exact_inverse(qq)
cc0,cc1,cc2=[vB(sp.Poly(W,XB))*qinv%Fexact for W in (C0,C1,C2)]
assert cc0!=0
Ea=[-192*cc0,fmpq_poly([]),25*cc2,fmpq_poly([25])]
Eb=[-48*cc0,-8*cc1,15*cc2]
def trim(a):
    a=list(a)
    while a and a[-1]==0:a.pop()
    return a
Ea,Eb=trim(Ea),trim(Eb)
trace=[]
while Eb:
    trace.append((len(Ea),len(Eb)))
    Ea,Eb=Eb,grem(Ea,Eb)
assert len(Ea)==2
arel=-Ea[0]*exact_inverse(Ea[1])%Fexact
assert arel!=0
log('exact a gcd and every pivot',trace,'monic linear, a live')
def pev(g):
    return base.to([Fraction(x)for x in reversed(sp.Poly(g,XV).all_coeffs())])
ff=list(map(int,reversed(f.all_coeffs())))
assert ff[-1]%p
baseMod=monic_f(POL(ff)).factor()[1][args.residue_index][0]
v=base.gen()
def inv(x):
    g,y,_=x.f.xgcd(baseMod)
    assert g==1
    a=PE(y);assert a*x==1
    return a
b=-pev(h0)*inv(pev(h1))
# Avoid reducing the rational inverse found over QQ; only its exact
# coprimality was needed. All residue inverse witnesses are checked anew.
def bpol(Q):return ev([pev(Q.nth(i))for i in range(Q.degree()+1)],b)
assert bpol(FB)==bpol(G)==0
j4=pev(J4(XV))
lam=-pev(J5(XV))*inv(j4)
T5=[(base.to(c)+lam*a).scale(Fraction(1,132))for c,a in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
R3=cofact(cofact(T5,v),b)
c0,c1,c2,_=R3
one,zero=base.to(1),base.to(0)
S=base
def modrem(a,b):
    c=list(a); invb=inv(b[-1]);m=len(b)-1
    for i in range(len(c)-1,m-1,-1):
        q=c[i]*invb
        for j in range(m+1):c[i-m+j]-=q*b[j]
    assert all(x==0 for x in c[m:])
    return trim(c[:m])
ma0=trim([-192*c0,zero,25*c2,base.to(25)])
mb0=trim([-48*c0,-8*c1,15*c2])
rrt=[]
while mb0:
    rrt.append((len(ma0),len(mb0)))
    ma0,mb0=mb0,modrem(ma0,mb0)
assert rrt==trace and len(ma0)==2
av0=-ma0[0]*inv(ma0[1])
assert av0!=0
m=[5*av0*c0,16*c0,5*av0**2]
u0,u1,u2=m
p0=u1*u2*c0
q0=3*u0*u2*c2-4*u0*u1-3*u2*u2*c0
v,b,c0,c1,c2,one,zero=map(S.to,(v,b,c0,c1,c2,one,zero))
R3=list(map(S.to,R3))
old_matrix=cols(*(rem([zero]*i+list(m),R3)for i in range(3)))
ma=adjcol(old_matrix)
n,chk,chk2=rem(mul(m,ma),R3)
assert chk==chk2==0
J4p=list(map(S.to,(1,-14,56,-84,42)))
P0=[zero,*R3];P=[zero,*m]
IP=prim(P); IP0=prim(P0);I2P=prim(IP)
def fit(f):return rem(mul(ma,f),R3)
M=fit(J4p);W0=fit(IP0[1:]);ell=fit(IP[1:]);rho=fit(I2P[1:])
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

tt=T.gen()
v,b,l,pr,qr,nn=map(et,(v,b,one,p0,q0,n))
ZZ,OO=et(0),et(1)
RR,MT,WW,J4T,P0T,L0T=map(lift,(R3,M,W0,J4p,P0,IP0[1:]))
U=pplus(MT,pscale(RR,tt))
Rv=ev(RR,v);uV=ev(U,v)
jV=ev(J4T,v);jB=ev(J4T,b)
JI=prim(mul([l,-OO],U))
Jb=ev(JI,l)-ev(JI,b)
assert Jb.degree<=1
def c(f,i):
    return f.cs[i] if i<len(f.cs) else zero
C0,C1=c(Jb,0),c(Jb,1)

# Raw matched primitive, with no division by V-z or by a leader.
Z=[-pr,qr];zv=ev(Z,v)
P1,EL,RO=map(lift,(P,ell,rho))
Cq=ev(P0T,v)*uV
Kq=zv*(nn*v*jV-ev(P1,v)*uV)
Qq=pplus(pscale(mul(Z,P1),Cq),pscale(P0T,Kq))
Lq=pplus(pscale(pplus(mul(Z,EL[:2]),pscale(RO,-qr)),Cq),pscale(WW,Kq))
IQ=prim(Qq)
hv=uV*ev(IQ,v)-v*jV*ev(Lq,v)
hbq=ev(U,b)*ev(IQ,b)-b*jB*ev(Lq,b)
assert hv.degree<=2 and hbq.degree<=2
def pin(h):
    return C1**2*c(h,0)-C1*C0*c(h,1)+C0**2*c(h,2)

def basis(r):
    if r is base:return [base.to(1)]
    return [r.gen()**i for i in range(r.n)]
def vect(x):
    if isinstance(x,PE):return [x.f]
    return [a.f for a in x.cs]
bb=basis(S);d=len(bb);assert d==1
def rank(es):
    piv={}
    for row in es:
        for m in bb:
            col=vect(row*m)
            for i in range(d):
                if col[i]==0:continue
                u=col[i]
                if i in piv:
                    h=piv[i]
                    for j in range(i+1,d):col[j]=(col[j]-u*h[j])%baseMod
                else:
                    g,iv,_=u.xgcd(baseMod)
                    assert g==1 and u*iv%baseMod==1
                    piv[i]=[None]*(i+1)+[a*iv%baseMod for a in col[i+1:]]
                    break
    return len(piv)
rows=[pin(hv),pin(hbq)]
log('residue',baseMod,'ranks',rank(rows[:1]),rank(rows),'dimension',d,
    'J1 rank',rank([C1]),'adjugate rank',rank([n]),'q rank',rank([q0]))
assert rank(rows)==d
