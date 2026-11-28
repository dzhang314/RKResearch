#!/usr/bin/env python3
"""Exact alpha-one zero-multiplier clock projection and guarded ranks.

Projections are computed over Q. Residue matrices exhibit nonvanishing
minors of matrices over the exact projected clock fields.
"""
from fractions import Fraction
from math import lcm,gcd,comb
from time import monotonic
import argparse
from flint import fmpq,fmpq_poly,nmod_poly,nmod_mat
parser=argparse.ArgumentParser()
parser.add_argument('tower',choices=('Fn0','F10','F1x','F2x','Fnx'))
args=parser.parse_args()
baseMod=None
p=0
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
        assert f.degree()==0,(name,'unexpected scalar removal',f)
        xs=tuple(x.div_exact(d)for x in xs)
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
if args.tower in ('F10','F1x'):
    Fn=[-75*c0*c0,75*c0*c2,-80*c1,K.to(96)]
elif args.tower=='F2x':
    Fn=[-c0*c0,c0*c2,-c1,K.to(1)]
L3=Fn[-1]
S=R(K,[Fn[i]*L3**(2-i)for i in range(3)],'Fn quadratic profile')
ss=S.gen()
B,L3,c0,c1,c2,L=(S.to(x)for x in (B,L3,c0,c1,c2,L))
V=S.to(v)*L
a,b=L-V,L-B
zero,one=S.to(0),S.to(1)
R3=[c0,c1,c2,one]
if args.tower=='F10':
    t1=16*ss
    t0=15*(c2*ss-c0*L3)
elif args.tower=='F1x':
    t1=16*c0*ss*L3*L3
    t0=16*ss*ss*(2*ss+c1*L3)-15*c0*(c2*ss-c0*L3)*L3*L3
elif args.tower=='F2x':
    t1=c0*ss*L3*L3
    t0=ss*ss*(2*ss+c1*L3)-c0*(c2*ss-c0*L3)*L3*L3
elif args.tower=='Fnx':
    t1=c0*(c1*L3+6*ss)*L3*L3
    t0=ss*(2*ss+c1*L3)*(c1*L3+6*ss)-6*c0*c2*ss*L3*L3
else:
    t1=c1*L3+6*ss
    t0=6*c2*ss
A1_TERMS=[((5, 0, 1, 0), -30), ((4, 1, 0, 1), 46), ((4, 0, 2, 1), 60), ((4, 0, 0, 2), 276), ((3, 1, 1, 2), -92), ((3, 0, 3, 2), -30), ((3, 0, 1, 3), -834), ((2, 2, 0, 3), 47), ((2, 1, 2, 3), 46), ((2, 1, 0, 4), 424), ((2, 0, 2, 4), 558), ((2, 0, 0, 5), 852), ((1, 2, 1, 4), -47), ((1, 1, 1, 5), -520), ((1, 0, 1, 6), -1044), ((0, 3, 0, 5), 16), ((0, 2, 0, 6), 160), ((0, 1, 0, 7), 448), ((0, 0, 0, 8), 384)]
A1gate=sum(n*c0**i*c1**j*c2**k*ss**h*L3**(8-h)for (i,j,k,h),n in A1_TERMS)
m=lose('common m scale',ss*t1,t0*L3,t1*L3)
old_matrix=cols(*(rem([zero]*i+list(m),R3)for i in range(3)))
den=det(old_matrix)
J4p=[L**4,-14*L**3,56*L**2,-84*L,42*one]
H=[zero,*J4p]
def refl(f):
    return [(-1)**i*sum(comb(j,i)*f[j]*L**(j-i)for j in range(i,len(f))) for i in range(len(f))]
U=pscale(refl(R3),-one)
D=mul([-L,one],mul([-V,one],[-B,one]))
K0=rem(mul(J4p,D),R3)
K1=rem([zero,*K0],R3)
def det_gate(f):
    return det(cols(K0,K1,rem(f,R3)))
def masked(both):
    f=mul([zero,-b,one],U)
    if both: f=mul(f,[-a,one])
    F=prim(f)
    fa,fb,ha,hb=ev(F,a),ev(F,b),ev(H,a),ev(H,b)
    if both:
        c=[a*fb*ha-b*fa*hb,fa*hb-fb*ha]
        P=pplus(pscale(F,ha*hb*(a-b)),pscale(mul(H,c),-one))
    else:
        P=pplus(pscale(F,hb),pscale(H,-fb))
    assert P[0]==0
    return rem(refl(P),R3)
u0,u1,u2=m
zp=u1*u2*c0
zq=3*u0*u2*c2-4*u0*u1-3*u2*u2*c0
E7=det_gate(mul(list(m),masked(True)))
E6=det_gate(mul(mul(list(m),[-zp,zq]),masked(False)))
d0=ev(R3,V);d1=ev(prim([zero,*R3])[1:],V)
Jm=ev(prim([zero,*m])[1:],V)
Adj=(zp-V*zq)*(d1*ev(m,V)-d0*Jm)-zq*d1*Jm

# Chronology-specific extra gates.
mark5=prim(mul([-V,one],[zero,*R3]))[1:]
J4V=ev(J4p,V)
N5=rem(pplus(pscale(mark5,J4V),pscale(J4p,-ev(mark5,V))),R3)
NY=rem([zero,*N5],R3)
H5=rem(mul([-V,one],J4p),R3)
J=prim([zero,*U])
B2=ev(J,b)**2*det(cols(N5,NY,H5))
# Q5 is the quintic error after fitting the old values and pinning z.
ma=adjcol(old_matrix)
Q0=rem(mul(ma,N5),R3)
def homog(f,x,d): return sum(f[i]*x**i*d**(len(f)-1-i)for i in range(len(f)))
rz=homog(R3,zp,zq)
qz=homog(Q0,zp,zq)
Qt=pplus(pscale(Q0,rz),pscale(R3,-zq*qz))
dd=[zq*zq*Qt[1]+zp*zq*Qt[2]+zp*zp*Qt[3],
    zq*zq*Qt[2]+zp*zq*Qt[3],zq*zq*Qt[3]]
jf=rem(refl(J),R3)
jf=rem(mul(mul(list(m),[-zp,zq]),jf),R3)
g1,g0=det_gate(jf),det_gate([zero,*jf])
B1=homog(dd,g0,g1)

# Nonconstant contents have already been checked against the known
# forbidden Jacobi/endpoint guard. No division by a profile variable
# enters either B1 or B2.
assert E7==0
if args.tower=='F10':assert Adj==0
else:assert Adj!=0
primary=[('E6',E6)]
if Adj!=0: primary.append(('Adj',Adj))
if args.tower.endswith('x'):primary.append(('A1',A1gate))

def norm_down(e):
    while isinstance(e,E):e=norm(e)
    return e.f

def projection(name,e):
    e,=lose(name+' input',e)
    while isinstance(e,E):
        e=norm(e)
        if isinstance(e,E):e,=lose(name+' relative',e)
    log(name,'exact projection degree',e.f.degree())
    return e.f/e.f.leading_coefficient()

P={}
for name,e in primary:
    P[name]=projection(name,e)
target={
    'Fn0':{'E6':720,'Adj':672},
    'F10':{'E6':368},
    'F1x':{'E6':512,'Adj':464,'A1':352},
    'F2x':{'E6':512,'Adj':464,'A1':352},
    'Fnx':{'E6':1152,'Adj':1104,'A1':768}
}[args.tower]
assert {n:f.degree() for n,f in P.items()}==target
F=P['E6']
for f in P.values():F=F.gcd(f)
assert F.degree()==dict(Fn0=588,F10=368,F1x=224,F2x=224,Fnx=576)[args.tower]
Jp=fmpq_poly([1,-14,56,-84,42]); Je=fmpq_poly([3,-32,108,-144,66])
Jm=fmpq_poly([1,-16,72,-120,66]); Jr=fmpq_poly([3,-64,604,-3096,9360,-17136,18648,-11088,2772])
x=fmpq_poly([0,1]); JJ=fmpq_poly([-1,20,-120,300,-330,132])
assert 2*x*Je==JJ+Jp and 2*(x-1)*Jm==JJ-Jp
assert 2*Jr==JJ.derivative()*Jp-JJ*Jp.derivative()
def monic(f):return f/f.leading_coefficient()
# (degree, constant coefficient) maps to multiplicity, beta-one
# live guard, exact upper rank, and residue extension degree.
recipes={
 'Fn0':{
   (120,6375864437904605062500000000):(1,None,12,11),
   (12,16227):(3,'profile-ratio',11,12),
   (12,54123):(20,'c2',9,4)
 },
 'F10':{
   (24,364663909217):(1,'zq',11,3),
   (108,-16344301879687500000000000000):(1,None,12,1),
   (24,72):(3,None,12,1)
 },
 'F1x':{},
 'F2x':{},
 'Fnx':{
   (48,41521530286435):(1,'zq',11,1),
   (12,54123):(18,'c2',9,4)
 }
}[args.tower]
ends={
'Fn0':(39,9),'F10':(17,24),'F1x':(26,30),'F2x':(26,30),'Fnx':(54,24)
}[args.tower]
gs={'c2':c2,'profile-ratio':t1,'zq':zq}
norms={}
to_check=[]
seen=set()
guard_powers=[0,0]
for f,k in F.numer().factor()[1]:
    f0=fmpq_poly(f)
    hit=next((i for i,e in enumerate((Jp,Je))if monic(e)==monic(f0)),None)
    if hit is not None:
        assert guard_powers[hit]==0
        guard_powers[hit]=k
        continue
    ID=(f.degree(),int(f[0]))
    assert ID not in seen
    seen.add(ID)
    ex,g,cap,degree=recipes[ID]
    assert ex==k
    if g is not None:
        if g not in norms: norms[g]=norm_down(gs[g])
        assert norms[g]!=0 and norms[g]%f0==0
    to_check.append((f,g,cap,degree))
assert tuple(guard_powers)==ends and seen==set(recipes)
log('exact joint degree',F.degree(),'forbidden factors',ends,'other support',list(recipes))

def rank_tests(f,k,cap,d):
    global p,baseMod
    p=103
    ff=nmod_poly(list(map(int,f.coeffs())),p)
    assert ff.degree()==f.degree()
    ff=sorted((c for c,_ in ff.factor()[1]),
              key=lambda c:(c.degree(),list(map(int,c.coeffs()))))[0]
    assert ff.degree()==d
    baseMod=ff
    chain={}
    def cv(e):
        if isinstance(e,PE):
            return PE(nmod_poly([int(x.numerator)*pow(int(x.denominator),-1,p)%p
                                  for x in e.f.coeffs()],p))
        rr=e.r
        if id(rr) not in chain:
            mm=[cv(x)for x in rr.mod]
            lo=base if rr.low is base else chain[id(rr.low)]
            chain[id(rr)]=R(lo,mm,rr.name)
        return E(chain[id(rr)],tuple(cv(x)for x in e.cs))
    es=[cv(e)for _,e in primary]+[cv(B1)]
    other=cv(B2)
    top=es[0].r
    g=top.to(1) if k is None else cv(gs[k])
    def vec(e):
        if isinstance(e,PE):
            a=list(map(int,e.f.coeffs()))
            return a+[0]*(d-len(a))
        return sum([vec(x)for x in e.cs],[])
    def basis(r):
        if r is base:return [base.gen()**i for i in range(d)]
        lo=basis(r.low)
        return [r.to(x)*r.gen()**i for i in range(r.n)for x in lo]
    bs=basis(top)
    assert len(bs)==12*d
    def rank(elements):
        cols0=[vec(o*b)for o in elements for b in bs]
        return nmod_mat(list(map(list,zip(*cols0))),p).rank()
    r1=rank([g*e for e in es]);r2=rank([other])
    assert r1==cap*d and r2==12*d
    log('residue ranks over F_103',
        f.degree(),int(f[0]),'degree',d,'beta1',k,r1,'beta2 unit',r2)
    p=0;baseMod=None

for f,k,cap,d in to_check:
    rank_tests(f,k,cap,d)
log('both beta counts excluded in',args.tower)
