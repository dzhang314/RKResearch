#!/usr/bin/env python3
"""Exact / mod-p projections for the normalized DIRK11 invisible-six live cubic.
Source calculations by the finite clock algebra; modular mode alone is not a
characteristic-zero proof. Coordinates v and B are scaled by 132 J4(B).
"""
from fractions import Fraction
from itertools import permutations,combinations
from math import lcm,gcd
from pathlib import Path
import sys
from time import monotonic
import argparse
from flint import fmpq,fmpq_poly,nmod_poly
parser=argparse.ArgumentParser()
parser.add_argument('--p',type=int,default=101)
parser.add_argument('--chart',choices=('five','pair','all'),default='all')
parser.add_argument('--write',type=Path)
parser.add_argument('--no-extra',action='store_true')
parser.add_argument('--first-only',action='store_true')
parser.add_argument('--raw',action='store_true')
parser.add_argument('--trace-guards',action='store_true')
parser.add_argument('--verify-over',type=Path)
parser.add_argument('--verify-prime',type=int,default=101)
parser.add_argument('--prefix-together',action='store_true')
args=parser.parse_args()
baseMod=None
p=args.p
t0=monotonic()
def log(*x): print(f'{monotonic()-t0:8.2f}',*x,flush=True)
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
def lose(name,*xs,strip=True):
    global ledger
    if args.verify_over and p:return xs
    d=content(*xs)
    if d.degree() and strip:
        ledger.append((name,d));xs=tuple(x.div_exact(d)for x in xs)
    if not p:
        fs=sum([flatten(x)for x in xs],[])
        l=lcm(*(int(f.denom())for f in fs))
        g=gcd(*(int(f.numer().content())*(l//int(f.denom()))for f in fs))
        if g:xs=tuple(x.scale(Fraction(l,g))for x in xs)
    log(name,'deg',max(a.degree()for x in xs for a in flatten(x)),'content',d.degree() if strip else 'uncleared')
    return xs
def homog(f,x,d):
    return sum(x.r.to(c)*x**i*d**(len(f)-1-i)for i,c in enumerate(f))
ledger=[]
b=base.gen()
j4=lambda y:42*y**4-84*y**3+56*y*y-14*y+1
j5=lambda y:(2*y-1)*(66*y**4-132*y**3+84*y*y-18*y+1)
L=132*j4(b)
T5raw=pplus(pscale([base.to(c)for c in (-1,20,-120,300,-330,132)],j4(b)),pscale([base.to(c)for c in (1,-14,56,-84,42)],-j5(b)))
assert T5raw[-1]==L
T4raw=cofact(T5raw,b)
T4=[T4raw[i]*L**(3-i)for i in range(4)]+[base.to(1)]
K=R(base,T4[:-1],'fourth ordinary')
V=K.gen()
R3=cofact(T4,V)
c0,c1,c2,_=R3
F3=[-3*V**2*c0**2,-6*V**2*c0*c2+2*V**2*c1**2-3*V*c0*c1+c0**2,
    8*V**2*c1-3*V**2*c2**2-6*V*c0+V*c1*c2-c0*c2,2*V*(4*V+c2)]
L3=F3[-1]
S=R(K,[F3[i]*L3**(2-i)for i in range(3)],'constant quadratic profile')
ss=S.gen()
V,L3,c0,c1,c2,L=(S.to(x)for x in (V,L3,c0,c1,c2,L))
bscaled=S.to(b)*L
z0,z1=S.to(0),S.to(1)
R3=[c0,c1,c2,z1]
# Reduced exact F3 pivot. The known discriminant exclusion implies
# c0+c2*s != 0, and the actual fourth ordinary V is nonzero.
Dsmall=V*(c0*L3+c2*ss)
Nsmall=ss*((c2+4*V)*ss+(2*V*c1-c0)*L3)
m=lose('common cubic-fit scaling',ss*Dsmall,Nsmall,L3*Dsmall)
J4=[L**4,-14*L**3,56*L**2,-84*L,42*z1]
h=[z0,*J4]
P=[z0,*m];P0=[z0,*R3]
IP,IP0,IY=prim(P),prim(P0),prim([z0,*P])
M=cols(*(rem([z0]*i+list(m),R3)for i in range(3)))
adj=adjcol(M)
# m*adj = d modulo R3. Common exact scalar factors may be discarded
# in adj only if d is changed by exactly the same scale.
adj=lose('common old-inverse scaling',*adj)
den,zero1,zero2=rem(mul(m,adj),R3)
assert zero1==zero2==0
def old(f): return rem(mul(adj,f[1:]),R3)
a,bb,ay=(old(f)for f in (IP,IP0,IY))
aV=ev(a,V); ipV=ev(IP,V); RV=ev(R3,V)
dl=den.scale(Fraction(1,4))*m[-1]-a[1]
Ad=pplus(pscale(a,aV),pscale(bb,dl))
Fd=pplus(pscale(ay,aV),pscale(bb,V*dl))
Ad0,Ad1,Ad2,Fd0,Fd1,Fd2,Den=lose('common reverse-marks scale',*Ad,*Fd,den*aV)
Ad=[Ad0,Ad1,Ad2]; Fd=[Fd0,Fd1,Fd2]
C=[Fd0,Fd1-Ad0,Fd2-Ad1,-Ad2]
Q5=prim(mul([-V,z1],P0))
def clean(f):
    rr=old(f)
    return pplus(pscale(rr,ipV*RV),pscale(R3,ev(f,V)*aV-ipV*ev(rr,V)))
U=lose('carrier',*clean(h))
Q=lose('clean quintic',*clean(Q5))
for name,x in [('first gap lead',C[-1]),('U lead',U[-1])]:log(name,max(a.degree()for a in flatten(x)))
# Cofactors/guard factors that arose from common content are only stripped
# in quotients for which the normalized upstream set is separately audited.
# For now the degree statistics are exploratory, not a safety certificate.
if args.verify_over:
    assert not p, 'build the complete upstream coefficients exactly'
    p=args.verify_prime
    coeff=[int(x)for x in args.verify_over.read_text().split()]
    f=nmod_poly(coeff,p)
    assert f.degree()==len(coeff)-1 and f.degree()>0
    baseMod=monic_f(f)
    log('switching to the proved degree-preserving reduction',p,baseMod.degree())
    done={}
    old=base
    def convert(g):
        if isinstance(g,PE):
            return PE(nmod_poly([int(x.numerator)*pow(int(x.denominator),-1,p)%p for x in g.f.coeffs()],p))
        A=g.r
        if id(A) not in done:
            op=[convert(x)for x in A.mod]
            lo=base if A.low is old else done[id(A.low)]
            done[id(A)]=R(lo,op,A.name)
        return E(done[id(A)],tuple(convert(x)for x in g.cs))
    # Convert every upstream Q coefficient, including all quotient
    # moduli. No symbolic branch-rank or rational normalization is used
    # in the downstream reduced norm.
    U,Q,C,Ad,Fd,T4,R3=[[convert(x)for x in a]for a in (U,Q,C,Ad,Fd,T4,R3)]
    L,bscaled,Den,z0,z1=(convert(x) for x in (L,bscaled,Den,z0,z1))
    S=z0.r
    Ad0,Ad1,Ad2=Ad
out={}
def project(name,x):
    global ledger
    if args.verify_over:
        while isinstance(x,E):x=norm(x)
        g,u,v=baseMod.xgcd(x.f)
        assert g==baseMod*u+x.f*v
        log(name,'exact residual degree',baseMod.degree(),'coprime gcd degree',g.degree())
        if args.write:
            (args.write/(name+'-bezout.txt')).write_text('\n'.join(' '.join(map(str,a.coeffs())) for a in [baseMod,x.f,g,u,v])+'\n')
        return g
    x,=lose(name+': extension numerator',x)
    while isinstance(x,E):
        x=norm(x)
        log(name+': norm',max(a.degree()for a in flatten(x)))
        if isinstance(x,E):x,=lose(name+': relative norm content',x)
    f=monic_f(x.f)
    out[name]=f
    if args.write:
        path=args.write/(name+'.txt')
        path.write_text(' '.join(map(str,f.coeffs()))+'\n')
    log(name+': base projection',f.degree())
    return f
def fold(name,x):
    while isinstance(x,E):
        x=norm(x)
        log(name,'norm',max(a.degree()for a in flatten(x)))
    return monic_f(x.f)
from functools import lru_cache
@lru_cache(maxsize=None)
def minors(d):
    # Constant cofactor matrix formed by U Y^k, k=0,...,d-3 in P_d.
    columns=[tuple([z0]*i+list(U)+[z0]*(d+1-len(U)-i))for i in range(d-2)]
    out=[]
    for ix in combinations(range(d+1),3):
        r=tuple(i for i in range(d+1)if i not in ix)
        h=(-1)**(sum(ix)-3)*det([[c[i]for c in columns]for i in r])
        if h!=0:out.append((ix,h))
    return out
def small_det(F,G,H,d):
    # Two marked polynomial columns are moderately large; regroup the
    # third-relative wedge so each marked coefficient product is formed
    # once, not once per complementary triple.
    ff,gg,hh=(list(a)+[z0]*(d+1-len(a))for a in (F,G,H))
    assert len(ff)==len(gg)==len(hh)==d+1
    w={}
    for (i,j,k),m in minors(d):
        if hh[k]!=0:w[i,j]=w.get((i,j),0)+hh[k]*m
        if hh[j]!=0:w[i,k]=w.get((i,k),0)-hh[j]*m
        if hh[i]!=0:w[j,k]=w.get((j,k),0)+hh[i]*m
    return sum((ff[i]*gg[j]-ff[j]*gg[i])*x for (i,j),x in w.items() if x!=0)
def cubic_adj_gate():
    # det in the polynomial space through degree 7, with the remaining
    # five columns U, Y U, ..., Y^4 U.  All W_j share the same scale.
    S6=mul(mul([L,-z1],[-bscaled,z1]),T4)
    S6=[S.to(x)for x in S6]
    f=prim(mul([L,-z1],U))
    F=pplus([ev(f,L)],pscale(f,-z1))
    j0=F;j1=[z0,*F];j2=[z0,z0,*F]
    # The curvature equation alone can be formed directly at degree six.
    w2=small_det(j0,j1,S6,6)
    if args.first_only:return F,S6,None,None,lose('gamma5 direct curvature numerator',w2)[0]
    w0=small_det(j1,j2,S6,7)
    w1=-small_det(j0,j2,S6,7)
    w0,w1,w2=lose('gamma5 homogeneous inverse',w0,w1,w2*U[-1])
    return F,S6,w0,w1,w2
if args.trace_guards:
    # Distinct guard roots can occur on *other* components.  The projections
    # here are not assertions that a selected valid clock misses their zeros.
    lprod=POL([1])
    ii=lambda f:f//f.gcd(f.derivative())
    aGuards=[('clock scale',L),('B 0 or 1',bscaled*(bscaled-L)),
        ('V 0 or 1 or B',V*(V-L)*(V-bscaled)),('C old constant',c0),
        ('R3 V',RV),('R3 B',ev(R3,bscaled)),('R3 1',ev(R3,L)),
        ('clock derivative',ev([T4[i]*i for i in range(1,5)],V)),
        ('F3 degree',L3),('F3 derivative',S.to(F3[1])*L3+2*S.to(F3[2])*ss+3*ss*ss),
        ('r denominator',Dsmall),('r numerator',Nsmall),('s numerator',ss),
        ('det m',den),('ell V numerator',aV),('I(P)(V)',ipV),
        ('slope plus one',a[1]+den),('U leading',U[-1]),
        ('U at 1 or B',ev(U,L)*ev(U,bscaled)),('first gap leader',C[-1])]
    for tag,g in aGuards:
        f=fold('guard '+tag,g)
        f=ii(f)
        if args.write:(args.write/('G'+tag+'.txt')).write_text(' '.join(map(str,f.coeffs()))+'\n')
    raise SystemExit(0)
if args.chart in ('five','all'):
    invData=cubic_adj_gate()
    J,S0,W0,W1,W2=invData
    if not args.verify_over:fj=project('five-curvature',W2)
    if args.first_only:
        if args.write:(args.write/'ledger.txt').write_text('\n'.join(name+' '+ ' '.join(map(str,d.coeffs())) for name,d in ledger)+'\n')
        raise SystemExit(0)
    Fz=homog(C,-W0,W1)
    gg=project('five-first-gap',Fz)
    if args.verify_over:raise SystemExit(0 if gg.degree()==0 else 1)
if args.chart in ('pair','all'):
    # Pair tests as compact polynomials in the unscaled first ghost z.
    # c_i(z)=F_i-z A_i, z+w=-c1/c2, zw=c0/c2.
    ds=[[Fd[i],-Ad[i]]for i in range(3)]
    a,bb0,cc=ds
    neg=lambda f:pscale(f,-z1)
    sq=lambda f:mul(f,f)
    wedge=lambda i,j:U[i]*Q[j]-U[j]*Q[i]
    Hdiv=[z0]
    for ii,jj,P in ((0,1,sq(cc)),(0,2,neg(mul(bb0,cc))),
        (0,3,pplus(sq(bb0),neg(mul(a,cc)))),(1,2,mul(a,cc)),
        (1,3,neg(mul(a,bb0))),(2,3,sq(a))):
        Hdiv=pplus(Hdiv,pscale(P,wedge(ii,jj)))
    hda=pplus(pscale(cc,Ad2*0+Ad1),pscale(bb0,-Ad2))
    hdu=pplus(pplus(pscale(sq(cc),U[1]),pscale(mul(bb0,cc),-U[2])),pscale(pplus(sq(bb0),neg(mul(a,cc))),U[3]))
    # A(w) c2^2 = (A0 c2-A2 c0)c2 - (c1+zc2)(A1 c2-A2 c1)
    r_at_w=pplus(mul(pplus(pscale(cc,Ad0),pscale(a,-Ad2)),cc),
                neg(mul(pplus(bb0,[z0,*cc]),hda)))
    Rdiv=pplus(pplus(pscale(mul(U,r_at_w),Den),neg(mul(mul(mul(U,Ad),hda),cc))),mul(sq(Ad),hdu))
    # The projected tests use a Sylvester determinant in rank d+3,
    # pre-eliminated in y by ordinary pseudoremainder.  A cubic root
    # also remains a root of each pseudoremainder if C3 is live.
    def pprem(P,Q):
        zero=z0
        O=list(P)
        for _ in range(len(P)-len(Q)+1):
            lead=O[-1]; d=len(O)-len(Q)
            O=pscale(O,Q[-1])
            for rr,vv in enumerate(Q):O[rr+d]-=lead*vv
            assert O[-1]==0
            O.pop()
        return O
    Hdiv=list(lose('pair quintic coefficients',*Hdiv))
    def small_res(P,Q):
        n,m=len(P)-1,len(Q)-1
        matrix=[]
        for i in range(m):matrix.append([z0]*i+list(P)+[z0]*(m-1-i))
        for j in range(n):matrix.append([z0]*j+list(Q)+[z0]*(n-1-j))
        return det(matrix)
    if not args.verify_over:
        q1=small_res(C,Hdiv)
        f=project('pair-quintic',q1)
    if args.first_only:
        if args.write:(args.write/'ledger.txt').write_text('\n'.join(name+' '+ ' '.join(map(str,d.coeffs())) for name,d in ledger)+'\n')
        raise SystemExit(0)
    if not args.no_extra:
        if args.chart!='all':invData=cubic_adj_gate()
        J,S6,_,_,_=invData
        S1=[z0,*S6]
        D0,D1,D2=lose('gamma4 prefix minors',*(small_det([z0]*i+list(J),S6,S1,7)for i in range(3)))
        ph=pplus(pplus(pscale(cc,D2),pscale(bb0,D1)),pscale(a,D0))
        project('four-prefix',homog(C,-ph[0],ph[-1]))
        project('four-prefix-quintic',homog(Hdiv,-ph[0],ph[-1]))
    if not args.prefix_together:
        Rdiv=list(lose('pair reverse coefficients',*pprem(Rdiv,C)))
        r1=small_res(C,Rdiv)
        gg=project('pair-commutator',r1)
        if args.verify_over:raise SystemExit(0 if gg.degree()==0 else 1)
for group in (['five-curvature','five-first-gap'],['pair-quintic','pair-commutator','four-prefix','four-prefix-quintic']):
    fs=[out[k]for k in group if k in out]
    if len(fs)>1:
        log('gcd',group[:len(fs)],[f.degree()for f in fs])
        g=fs[0]
        for f in fs[1:]:
            g=g.gcd(f)
            log('gcd degree',g.degree())
            if p:log('gcd factors',[(a.degree(),e, str(a) if a.degree()<=14 else '')for a,e in g.factor()[1]])
if args.write:
    (args.write/'ledger.txt').write_text('\n'.join(name+' '+ ' '.join(map(str,d.coeffs())) for name,d in ledger)+'\n')
