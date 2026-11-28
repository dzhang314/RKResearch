"""Six-zero three-off-clock active chart: arithmetic front at physical row four."""
import sys
rear=sys.argv[1]
mate=int(sys.argv[2])
from flint import fmpq, fmpq_poly, fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx
from time import monotonic
t0=monotonic()
def now(*a):print(round(monotonic()-t0,2),*a,flush=True)
def Q(a,b=1):return fmpq(a,b)
CV0=fmpq_poly()
class V:
    """Quadratic coefficients; v^2=2v+1."""
    def __init__(self,*f):
        if len(f)==1 and isinstance(f[0],V): self.c=f[0].c; return
        if len(f)==1 and isinstance(f[0],(int,fmpq)): f=(fmpq_poly([f[0]]),)
        self.c=tuple(f)+(CV0,)*(3-len(f))
    def __bool__(self):return any(self.c)
    def __eq__(self,y):return self.c==V(y).c
    def __neg__(self):return V(*(-x for x in self.c))
    def __add__(self,y):
        if getattr(y,"depth",0)>0:return NotImplemented
        return V(*(x+z for x,z in zip(self.c,V(y).c)))
    __radd__=__add__
    def __sub__(self,y):
        if getattr(y,"depth",0)>0:return NotImplemented
        return self+-V(y)
    def __rsub__(self,y):return -self+V(y)
    def __mul__(self,y):
        if getattr(y,"depth",0)>0:return NotImplemented
        a,b,c=self.c;d,e,f=V(y).c
        h0=a*d;h1=a*e+b*d;h2=a*f+b*e+c*d;h3=b*f+c*e;h4=c*f
        return V(h0+h2+2*h3+5*h4,h1+2*h2+5*h3+12*h4,CV0)
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return V(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def degree(self):return max(x.degree() for x in self.c)
    def coeff(self,j):return V(*(fmpq_poly([x[j]]) for x in self.c))
    def shift(self,n):return V(*(x.left_shift(n) for x in self.c))
    def adj_norm(self):
        a,b,c=self.c
        assert not c
        adj=V(a+2*b,-b,CV0)
        N=a*a+2*a*b-b*b
        assert self*adj==V(N)
        return adj,N
    def invconst(self):
        assert self.degree()==0
        adj,N=self.adj_norm()
        return V(*(x/N[0] for x in adj.c))
    def divrem(self,d):
        assert d
        if self.degree()<d.degree():return V(0),self
        adj,N=d.adj_norm()
        q=V(*(x//N for x in (self*adj).c))
        r=self-q*d
        assert r.degree()<d.degree()
        return q,r
    def __mod__(self,d):return self.divrem(d)[1]
    def exact(self,d):
        q,r=self.divrem(d)
        assert not r
        return q
    def monic(self):
        return self*self.coeff(self.degree()).invconst() if self else self
    def gcd(self,d):
        x,y=self,d
        if y.degree()>x.degree():x,y=y,x
        while y:
            x,y=y,x%y
        return x.monic()
    def reduce(self,ctx,p,v):
        assert all(int(x.denominator)%p for pol in self.c for x in pol.coeffs())
        s=ctx.zero()
        for i,pol in enumerate(self.c):
            s+=ctx([int(x.numerator)*pow(int(x.denominator),-1,p)%p*v**i for x in pol.coeffs()])
        return s
    def __repr__(self):return str(self.c)

v=V(CV0,fmpq_poly([1]),CV0)
u=V(fmpq_poly([0,1]))
assert v*v==2*v+1
D=2+mate*u
w=2*v if rear=='arith' else 2-v
t=D-1-v;s=D-1-w
pR=(1+2*w-w*w+2*w*v)*(2*v).invconst()
H=-2+u+4*u*u-u**3;j=3*u-2
p0=-H+j*(1+u);p1=2*H-j*(2+u);L=-H*Q(1,2)+j
assert L*2==(u-1)**2*(u-2)
f2=3*p1*Q(1,2)-3*L;f1=3*(p0-p1);f0=-3*p0
def det(M):
    x,y,z=M
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
def ext3(Base,depth0,rel):
 class E:
    depth=depth0
    def __init__(self,*cs):
        if len(cs)==1:
            if isinstance(cs[0],E): self.c=cs[0].c;return
            cs=(Base(cs[0]),Base(0),Base(0))
        self.c=cs
    def __bool__(self):return any(self.c)
    def __eq__(x,y):return x.c==E(y).c
    def __neg__(x):return E(*(-c for c in x.c))
    def __add__(x,y):
        if getattr(y,"depth",0)>depth0:return NotImplemented
        return E(*(a+b for a,b in zip(x.c,E(y).c)))
    __radd__=__add__
    def __sub__(x,y):
        if getattr(y,"depth",0)>depth0:return NotImplemented
        return x+-E(y)
    def __rsub__(x,y):return -x+E(y)
    def __mul__(x,y):
        if getattr(y,"depth",0)>depth0:return NotImplemented
        yz=E(y).c
        out=[Base(0)]*5
        for i,a in enumerate(x.c):
            if a:
                for j,b in enumerate(yz):
                    if b:out[i+j]=out[i+j]+a*b
        for k in range(4,2,-1):
            if out[k]:
                for i in range(3):
                    out[i+k-3]=out[i+k-3]-out[k]*rel[i]
        return E(*out[:3])
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return E(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def norm(x):
        sy=E(Base(0),Base(1),Base(0))
        c=(x.c,(x*sy).c,(x*sy*sy).c)
        return det([list(z) for z in zip(*c)])
    def coeffs(x):
        if depth0==1:return list(x.c)
        return [u for v in x.c for u in v.c]
    def deg(x):return max(v.degree() for v in x.coeffs())
    def divide(x,d):
        if depth0==1:return E(*(c.exact(d) for c in x.c))
        return E(*(c.divide(d) for c in x.c))
 return E
U=ext3(V,1,[f0*L*L,f1*L,f2])
A=U(V(0),V(1),V(0))
U0=A-A
def M(j):return D**j*Q(1,j+1)
def mm(j):
    return U(L*M(j+3))-(U(L*(s+t))+A)*M(j+2)+(U(L*s*t)+A*(s+t))*M(j+1)-A*s*t*M(j)
def mr(j):
    def h(z):
        return U(L*M(j+2))-(U(L*z)+A)*M(j+1)+A*z*M(j)
    return h(t)*pR-h(s)*v
mom=[mm(j) for j in range(5)]
rs=[mr(j) for j in range(4)]
MM=[[mom[0],mom[1],mom[2]],[mom[1],mom[2],mom[3]],[rs[0],rs[1],rs[2]]]
delta=det(MM)
rhs=[-mom[3],-mom[4],-rs[3]]
cn=[]
for i in range(3):
    Md=[z[:] for z in MM]
    for j in range(3):Md[j][i]=rhs[j]
    cn.append(det(Md))
n0,n1,n2=cn
for i in range(3):
    assert sum((MM[i][j]*cn[j] for j in range(3)),U(0))==rhs[i]*delta
g=Wg=delta*L
W=ext3(U,2,[n0*delta*delta*L**3,n1*delta*L**2,n2*L])
X=W(U(0),U(1),U(0));A0=W(A*delta);Sa=W(g*s);Ta=W(g*t);Ga=W(g);Da=W(g*D)
P=[W(p0)*Ga*Ga,W(p1)*Ga,W(L)]
def L4(z):return 70*z**4-140*Da*z**3+90*Da**2*z*z-20*Da**3*z+Da**4
def ev(z):return sum((a*z**i for i,a in enumerate(P)),W(0))
def J(k,z):return sum((a*z**(i+k+1)*Q(1,i+k+1) for i,a in enumerate(P)),W(0))
FWD=L4(A0)*(A0*(J(0,X)-Ga*ev(X))+Ga*X*ev(X)-J(1,X))-L4(X)*(Ga*A0*ev(A0)-J(1,A0))
# Build the ordinary six-node polynomial and cardinal numerator directly as
# coefficient lists, to avoid treating the prospective root as a variable.
def mul(a,b):
    c=[U(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=c[i+j]+x*y
    return c
Q3=[n0*delta*delta*L**3,n1*delta*L**2,n2*L,U(1)]
P6=mul(mul(mul([-A*delta,U(1)],[-g*s,U(1)]),[-g*t,U(1)]),Q3)
Bcoeff=[sum((P6[k]*(g*D)**(k-i-1)*Q(1,k-i) for k in range(i+1,7)),U(0)) for i in range(6)]
B=lambda y:sum((W(c)*y**i for i,c in enumerate(Bcoeff)),W(0))
R=[Sa*Ta,-Sa-Ta,W(1)]
RJ=lambda y:sum((c*y**(i+1)*Q(1,i+1) for i,c in enumerate(R)),W(0))
RB=lambda y:RJ(Da)-RJ(y)
BWD=(Ga*(X-Sa)*(X-Ta)-RB(X))*B(X)+RB(Ta)*B(Ta)
def strip_e(a,guards):
    for z in guards:
        while True:
            h=z
            for y in a.coeffs():
                h=h.gcd(y)
                if h.degree()==0:break
            if h.degree()==0:break
            a=a.divide(h)
    return a
now("element degrees",FWD.deg(),BWD.deg(),delta.deg())
guards=[L,D,H,u,1+2*u-u*u]
nF=strip_e(FWD,guards).norm()
nR=strip_e(BWD,guards).norm()
now("inner norms",nF.deg(),nR.deg())
NN=[strip_e(t,guards).norm() for t in [nF,nR,nF+nR,delta,*cn]]
now("projected degrees",[(n.degree()) for n in NN])

# Convert the exact quadratic coefficient basis to SymPy only for small
# factor polynomials. All high-degree norms above use FLINT rational polys.
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
vv=S.Symbol('vv')
K=S.QQ.algebraic_field((S.Poly(vv*vv-2*vv-1,vv),vv))
R,X=ring('X',K)
def vp(a):
    vals=[[S.Rational(str(z)) for z in c.coeffs()] for c in a.c]
    n=max(map(len,vals))
    return R.from_dict({(i,):sum((K.convert(c[i])*K.unit**j for j,c in enumerate(vals) if i<len(c)),K.zero)
                        for i in range(n)})
def pv(a):
    gs=[];n=max(a.degree()+1,0)
    for i in range(n):
        c=a.get((i,),K.zero).to_list()[::-1]
        gs.append([Q(S.Rational(str(v)).p,S.Rational(str(v)).q) for v in c]+[Q(0)]*(3-len(c)))
    return V(*(fmpq_poly([x[j] for x in gs]) for j in range(3)))
assert vp(v)==K.unit and vp(u)==X
def strip_v(a,guards):
 for s0 in guards:
    while True:
        h=a.gcd(s0)
        if h.degree()==0:break
        a=a.exact(h)
 return a
ND=strip_v(NN[3],guards)
sG=strip_v(NN[3],guards)
for n in NN[4:]:sG=sG.gcd(strip_v(n,guards))
now("singular exact guarded common degree", sG.degree())
assert sG.degree()==0
ND_factors=vp(ND).factor_list()[1]
base_factors=[]
for z in guards:
    if z.degree()==0:continue
    for zz,e in vp(z).factor_list()[1]:
        zz=zz.monic()
        if zz not in base_factors:base_factors.append(zz)
base_factors=sorted(base_factors,key=lambda f:(f.degree(),str(f.as_expr())))
sups=[(pv(g.monic()),"base") for g in base_factors]+[(pv(f.monic()),"delta") for f,_ in ND_factors]
now("delta factor degrees",[(f.degree(),e) for f,e in ND_factors])
chosen=None
for p in (19,29,37,43,59,61,67,83,101,107,109,131,149,157,163,173,179):
    h=fmpz_mod_poly_ctx(p)([-1,-2,1])
    if h.factor()[1][0][0].degree()!=2:continue
    C=fq_default_ctx(modulus=h,var='v'); F=fq_default_poly_ctx(C); vw=C.gen()
    def M(f):return f.reduce(F,p,vw)
    try:
       ms=[M(n) for n in NN[:3]]
       rs=[M(a) for a,_ in sups]
    except (AssertionError,ValueError):
       continue
    if any(s.degree()!=t.degree() for s,t in zip(ms,NN)):continue
    if any(s.degree()!=t.degree() for s,(t,_) in zip(rs,sups)):continue
    current=ms[0].gcd(ms[1]).gcd(ms[2])
    orig=current
    exps=[]
    for h in rs:
        h=h.monic();k=0
        while current%h==F.zero():
            current=current//h
            k+=1
        exps.append(k)
    if current.degree()!=0:continue
    good=True
    for z in NN[:3]:
        for (h,nm),e in zip(sups,exps):
            if e==0:continue
            z,r0=z.divrem(h**e)
            if r0:
               good=False;break
        if not good:break
    if good:
       chosen=(p,[(a.degree(),k,e) for (a,k),e in zip(sups,exps) if e], orig.degree())
       break
now("exact divisor, gcd degree upper bound by good reduction",chosen)
assert chosen
def residue_factor(phi):
    def cr(x,p):
        n=S.Rational(str(x))
        return int(n.p)*pow(int(n.q),-1,p)%p
    def cv(c,vr,p):
        ans=0
        for b in c.to_list():ans=(vr*ans+cr(b,p))%p
        return ans
    def evV(z,uu,vv,p):return cv(vp(z).evaluate(X,K.convert(S.Integer(uu))),vv,p)
    for p in S.primerange(11,500):
        for vv,e in nmod_poly([-1,-2,1],p).roots():
            if e!=1:continue
            vv=int(vv)
            try:
               ph=nmod_poly([cv(phi.get((i,),K.zero),vv,p) for i in range(phi.degree()+1)],p)
            except ValueError:continue
            if ph.degree()!=phi.degree():continue
            for uu,e in ph.roots():
                if e!=1:continue
                uu=int(uu)
                try:
                   if any(evV(r,uu,vv,p)==0 for r in guards):continue
                   fa=nmod_poly([evV(z,uu,vv,p) for z in [f0*L*L,f1*L,f2]]+[1],p)
                   fd=nmod_poly([evV(z,uu,vv,p) for z in delta.c],p)
                   fg=nmod_poly([evV(z,uu,vv,p) for z in nF.c],p)
                   fh=nmod_poly([evV(z,uu,vv,p) for z in nR.c],p)
                except ValueError:continue
                g=fa.gcd(fg).gcd(fh)
                if g.degree()==1 and fa.gcd(fd)==g:
                   return p,vv,uu
    return None
for ff,e in ND_factors:
    ff=ff.monic()
    ans=residue_factor(ff)
    now('delta fiber',ff.degree(),'exact simple reduction proves only singular first-clock root',ans)
    assert ans
