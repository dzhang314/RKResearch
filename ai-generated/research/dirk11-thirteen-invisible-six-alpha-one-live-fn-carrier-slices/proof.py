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
parser.add_argument("--chart",choices=["zero-carrier","ghost-fifth"],required=True)
parser.add_argument("--factor",type=Path)
parser.add_argument("--out",type=Path)

args=parser.parse_args()
p=args.p
assert p==(103 if args.factor else 0)
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
    sig=(len(fargs)-1,fargs[0])
    baseMod=baseMod.factor()[1][0][0]
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
if args.chart=="global" or args.factor:
    Q_V=ev(Q4,v)
    rv=ev(RR,v);pv=ev(P0T,v);jv=ev(J4T,v)
    SM=pplus(pscale(MT,rv),pscale(RR,-ev(MT,v)))
    U=pplus(pscale(SM,Q_V),pscale(RR,nn*zeta*v*jv))
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
def coord(g,i):
    return g.cs[i] if i<len(g.cs) else zero
a0,a1,a2=lose('Adj',*Adj.cs)
assert a2!=0
# H = S[e]/(e²+a1 e+a2 a0) with the specialization e=a2 E.
H=R(S,[a2*a0,a1],'scaled adjacent carrier')
ee=H.gen()
def hom_remainder(name,g):
    # If g(E)=0, here g(e/a2) * a2^degree(g)=0.
    gg=lose(name,*g.cs)
    lead=a2
    v=H.to(gg[-1]); z=lead
    for f in reversed(gg[:-1]):
        v=v*ee+H.to(z*f)
        z=z*lead
    return H.to(0)+E(H,lose(name+' remainder',*v.cs))
def monic_norm(name,u):
    # Choose one seed projector only; preserve every non-forbidden V factor.
    assert u!=0
    e=norm(u)
    while isinstance(e,E):
        e,=lose(name+' relative norm',e)
        log(name,'relative degree',max(f.degree()for f in flatten(e)))
        e=norm(e)
    e,=lose(name+' final norm',e)
    f=e.f; sf=monic_f(f//f.gcd(f.derivative()))
    ff=sf if p else sf.numer()
    log(name,'raw/squarefree',f.degree(),sf.degree())
    fs=ff.factor()[1]
    log(name,'projection factors',[(g.degree(),int(g[0]))for g,_ in fs])
    if args.out:
        args.out.mkdir(exist_ok=True)
        for i,(g,e) in enumerate(fs):
            (args.out/(name+str(i)+'.txt')).write_text(' '.join(map(str,g.coeffs()))+'\n')
    return ff,fs
def relative_norm(x):
    while isinstance(x,E):x=norm(x)
    return x.f

std={(12,16227):('ratio',22,12),(12,54123):('c2',18,4)}
cases={
 'zero-carrier':{**std,(48,1865429207937):('q',22,1),(60,-1461941766456):('old',22,1),
                       (108,7261365757665534336793103761342611):('full',24,1)},
 'ghost-fifth':{**std,(60,99738554904):('full',24,3)}}
if not args.factor:
    f={'zero-carrier':a0,'ghost-fifth':B*zq-zp}[args.chart]
    _,fs=monic_norm(args.chart,f)
    signatures={(g.degree(),int(g[0]))for g,_ in fs}
    assert signatures==set(cases[args.chart]) and all(e==1 for _,e in fs)
    for g,e in fs:
        sig=(g.degree(),int(g[0]))
        guard,cap,_=cases[args.chart][sig]
        if guard=='full':continue
        gg={'ratio':t1,'c2':c2.cs[0],'q':zq,'old':den}[guard]
        N=relative_norm(gg)
        assert N!=0 and N%fmpq_poly(g.coeffs())==0
        log('exact cap',sig,guard,cap)
    raise SystemExit

QH=hom_remainder('Q',Qpin)
guard,cap,dd=cases[args.chart][sig]
assert baseMod.degree()==dd
gg={'ratio':t1,'c2':c2,'q':zq,'old':den,'full':one}[guard]
G=H.to(gg)**24
hs={'zero-carrier':ee,'ghost-fifth':H.to(B*zq-zp)}[args.chart]
def basis(r):
    if r is base:return [base.to(1)]
    lo=basis(r.low)
    return [r.to(x)*r.gen()**i for i in range(r.n)for x in lo]
bb=basis(H)
assert len(bb)==24
def pvect(e):
    if isinstance(e,PE):return [e.f]
    return sum([pvect(x)for x in e.cs],[])
def rank(es):
    piv={}
    for u in es:
        for x in bb:
            c=pvect(u*x)
            for i in range(24):
                if c[i]==0:continue
                if i in piv:
                    d=piv[i];a=c[i]
                    for j in range(i+1,24):c[j]=(c[j]-a*d[j])%baseMod
                    continue
                g,inv,_=c[i].xgcd(baseMod)
                assert g==1
                piv[i]=[None]*(i+1)+[c[j]*inv%baseMod for j in range(i+1,24)]
                break
            if len(piv)==24:return 24
    return len(piv)
r=rank([G*hs,G*QH])
log('joint image',args.chart,sig,guard,dd,r)
assert r==cap
