"""Division-free polynomial ordered-root norm in the final reflected-star chart."""
from flint import fmpq_poly as p, fmpq, nmod_poly
from time import monotonic
from itertools import permutations
import sympy as Sym
from sympy.polys.rings import ring
T0=monotonic()
def say(*x):print(round(monotonic()-T0,2),*x,flush=True)
g=p([0,1])
class Alg:
 def __init__(self, mod, base):
    self.n=len(mod);self.mod=mod;self.base=base
    self.b0=(lambda :p()) if base is None else (lambda :base.co(0))
 def co(self,x):
    if isinstance(x,El) and x.alg is self:return x
    if self.base is None:
      y=x if isinstance(x,p) else p([x])
    else:y=self.base.co(x)
    return El(self,[y]+[self.b0() for _ in range(self.n-1)])
 def gen(self):
    return El(self,[self.b0(), self.base.co(1) if self.base else p([1])]+[self.b0() for _ in range(self.n-2)])
class El:
 def __init__(self,A,cs):self.alg=A;self.cs=cs
 def __add__(a,b):
    b=a.alg.co(b)
    return El(a.alg,[x+y for x,y in zip(a.cs,b.cs)])
 __radd__=__add__
 def __sub__(a,b):
    b=a.alg.co(b)
    return El(a.alg,[x-y for x,y in zip(a.cs,b.cs)])
 def __rsub__(a,b):return a.alg.co(b)-a
 def __neg__(a):return El(a.alg,[-x for x in a.cs])
 def __bool__(a):return any(bool(x) for x in a.cs)
 def __mul__(a,b):
    A=a.alg
    b=A.co(b)
    r=[A.b0() for _ in range(2*A.n-1)]
    for i,x in enumerate(a.cs):
      if x:
       for j,y in enumerate(b.cs):
         if y:r[i+j]+=x*y
    for k in range(2*A.n-2,A.n-1,-1):
      x=r[k]
      if x:
       for j,m in enumerate(A.mod):
         if m:r[k-A.n+j]-=x*m
    return El(A,r[:A.n])
 __rmul__=__mul__
 def __pow__(a,j):
    r=a.alg.co(1)
    while j:
      if j&1:r=r*a
      j>>=1
      if j:a=a*a
    return r
 def __repr__(a):return f"{a.cs}"

def norm2(x):
 a,b=x.cs; c,d=x.alg.mod
 return a*a-a*b*d+b*b*c
def norm3(h,z):
 (a,b,c),(d,e,f),(g,h1,j)=[(h*z**i).cs for i in range(3)]
 return a*(e*j-f*h1)-b*(d*j-f*g)+c*(d*h1-e*g)

# Work over Q[v]/(v^3-4v^2-v+2) throughout the large fraction-free norm.
V=Alg([p([2]),p([-1]),p([-4])],None);v=V.gen()
gg=V.co(g)
vinv=(1+4*v-v*v)*fmpq(1,2)
assert not (v*vinv-1)
t=1+v
kap=1+2*v-v*v
alpha=kap*vinv**2*fmpq(1,2)
beta=-vinv**2
J1=fmpq(1,3)+v*fmpq(1,2)
qghost=-kap*J1*vinv*fmpq(1,2)
ell=[fmpq(1,70),fmpq(-2,7),fmpq(9,7),-2,1]
L=[V.co(c) for c in ell]
def evalc(cs,x):
 return sum((c*x**j for j,c in enumerate(cs)),V.co(0))
lls=evalc(L,gg);llt=evalc(L,gg*t)
Fghost=[1+v,-3-2*v,2+v*fmpq(1,2),V.co(fmpq(-1,3))]
line=[-(alpha*lls*t+beta*llt),alpha*lls+beta*llt]
rco=[qghost*L[i]*gg**i for i in range(5)]
for i,c in enumerate(Fghost):
 for j,b0 in enumerate(line):rco[i+j]+=c*b0
def remove_linear(co,root):
 out=[V.co(0) for i in range(len(co)-1)]
 out[-1]=co[-1]
 for i in range(len(out)-2,-1,-1):
   out[i]=co[i+1]+root*out[i+1]
 assert not (co[0]+root*out[0])
 return out
C,B,A=remove_linear(remove_linear(rco,V.co(1)),t)
E=Alg([A*C,B],V);e=E.gen()
# Inverse Hilbert matrix, now reproducing the two ghost atom masses.
Hinv=[[16,-120,240,-140],[-120,1200,-2700,1680],[240,-2700,6480,-4200],[-140,1680,-4200,2800]]
mom=[gg**j*(alpha+beta*t**j) for j in range(4)]
S=[sum((row[j]*mom[j] for j in range(4)),V.co(0)) for row in Hinv]
gE=E.co(g)
g_e=gE*e
Ss=sum((E.co(S[i]*A**(3-i))*g_e**i for i in range(4)),E.co(0))
Ls=sum((E.co(L[i]*A**(4-i))*g_e**i for i in range(5)),E.co(0))
scale=E.co(A)*Ss
sNorm=norm2(Ss)
def adeg(q):return max(c.degree() for c in q.cs)
say('scale norm',adeg(sNorm))
poly4=[scale**(3-i)*(scale*E.co(L[i])-Ls*E.co(S[i])) for i in range(4)]
s_e=g_e*Ss
q2=poly4[3]+s_e
q1=poly4[2]+s_e*q2
q0=poly4[1]+s_e*q1
assert not (poly4[0]+s_e*q0)
F=Alg([q0,q1,q2],E);a=F.gen()
q2b=F.co(q2)+a
q1b=F.co(q1)+a*q2b
G=Alg([q1b,q2b],F);b=G.gen()
scale=G.co(scale)
gsc=G.co(g)*scale
af=scale-G.co(a);bf=scale-b
polys=[[-gsc*gsc,2*gsc,G.co(fmpq(-1,2))],[gsc*gsc,-2*gsc,G.co(1)],[gsc*gsc,-gsc,G.co(0)]]
def val(poly,x):return poly[0]+poly[1]*x+poly[2]*x*x
def ini(poly,x):return sum((poly[j]*x**(j+1)*fmpq(1,j+1) for j in range(3)),G.co(0))
def Jx(poly,x):return sum((poly[j]*x**(j+2)*fmpq(1,j+2) for j in range(3)),G.co(0))
def LL(x):return 70*x**4-140*scale*x**3+90*scale*scale*x*x-20*scale**3*x+scale**4
la,lb=LL(af),LL(bf)
j0,j1,j2=[ini(p,af)-gsc*val(p,af) for p in polys]
f0,f1,f2=[la*(gsc*(bf-af)*val(p,bf)+af*ini(p,bf)-Jx(p,bf))-lb*(gsc*af*val(p,af)-Jx(p,af)) for p in polys]
say('formed scaled ordered early conditions')
pv=j2*f0-j0*f2
qv=j0*f1-j1*f0
pivot=j1*f2-j2*f1
R=-2*pv**3+qv*pv**2+4*qv**2*pv-qv**3-(3*qv-2*pv)*pv*pivot
say('cofactor cubic')
nB=norm2(R)
say('directed second-clock norm')
nA=norm3(nB,a)
say('first-clock norm')
nE=norm2(nA)
assert adeg(nE)==8868
say('raw norm degree',adeg(nE))


F4=Alg(poly4,E);v0=F4.gen()
dr=sum((F4.co(poly4[i])*i*v0**(i-1) for i in range(1,4)),F4.co(0))+4*v0**3
M=[(dr*v0**i).cs for i in range(4)]
disc=E.co(0)
for perm in permutations(range(4)):
 sign=(-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
 term=E.co(sign)
 for i in range(4):
   term*=M[i][perm[i]]
 disc+=term
Nd=norm2(disc);Nl=norm2(Ls)
def vmod(t,pr,z):
 out=nmod_poly([0],pr)
 for poly in reversed(t.cs):
   out=out*z+nmod_poly([int(c.numerator)*pow(int(c.denominator),-1,pr)%pr for c in poly.coeffs()],pr)
 return out
v0=Sym.Symbol('v')
K=Sym.QQ.algebraic_field((Sym.Poly(v0**3-4*v0**2-v0+2,v0),v0))
vv=K.unit
R0,D=ring('g',K)
def as_ring(t):
 out={}
 for i in range(adeg(t)+1):
   x=sum((K.convert(Sym.Rational(str(poly[i])))*vv**j for j,poly in enumerate(t.cs) if i<=poly.degree()),K.zero)
   if x:out[(i,)]=x
 return R0.from_dict(out)
def as_alg(t):
 out=[[] for i in range(3)]
 for i in range(t.degree()+1):
   a=t.get((i,),K.zero).to_list()[::-1]
   for j in range(3):out[j].append(fmpq(str(a[j])) if j<len(a) else 0)
 return El(V,[p(seq) for seq in out])
def trunc(t,d):
 return El(V,[x.truncate(d) for x in t.cs])
def rev(t,hi,l):
 return El(V,[p([x[hi-i] if hi-i<=x.degree() else 0 for i in range(l)]) for x in t.cs])
def exact_quo(num,den):
 dn,dd=adeg(num),adeg(den)
 qd=dn-dd
 if qd<0:return None
 T=rev(den,dd,qd+1)
 assert not (trunc(T,1)-1)
 inv=V.co(1);k=1
 while k<qd+1:
   m=min(2*k,qd+1)
   inv=trunc(inv*(2-trunc(T*inv,m)),m)
   k=m
 Q=rev(trunc(rev(num,dn,qd+1)*inv,qd+1),qd,qd+1)
 if num-Q*den:return None
 return Q


def monic_factor(t,m):
    fas=[f.monic() for f,n in as_ring(t).factor_list()[1] if f.degree()==m and n==1]
    return fas
aa=monic_factor(A,4)
assert len(aa)==1 and aa[0].degree()==4
aK=aa[0]
sK=monic_factor(sNorm,12)
assert len(sK)==2 and as_ring(sNorm).monic()==aK**3*sK[0]*sK[1]
def mod(poly,p0):
    return nmod_poly([int(c.numerator)*pow(int(c.denominator),-1,p0)%p0 for c in poly.coeffs()],p0)
sK_126=next(f for f in sK if mod(norm3(as_alg(f),v),101)%nmod_poly([16,94,1],101)==0)
sK_198=next(f for f in sK if mod(norm3(as_alg(f),v),101)(51)==0)
assert sK_126!=sK_198
guard=V.co(g)**48*as_alg(aK)**990*as_alg(sK_126)**126*as_alg(sK_198)**198
nReduced=exact_quo(nE,guard)
assert nReduced is not None and adeg(nReduced)==972
del nE,guard
outer=norm3(nReduced,v)
assert outer.degree()==2916
say('exact guarded degrees',adeg(nReduced),outer.degree())
Dout,Lout,Aout,Sout=[norm3(t,v) for t in (Nd,Nl,A,sNorm)]
main={f.degree():f/f.leading_coefficient() for f,m in outer.factor()[1]}
assert sorted((f.degree(),m) for f,m in outer.factor()[1])==[(36,18),(144,3),(1836,1)]
aGuard=norm3(as_alg(aK),v)
sGuard126=norm3(as_alg(sK_126),v)
sGuard198=norm3(as_alg(sK_198),v)
for f,dg in ((aGuard,12),(sGuard126,36),(sGuard198,36)):
    assert f.degree()==dg and len(f.factor()[1])==1 and f.factor()[1][0][1]==1
assert Aout.degree()==12 and Aout.gcd(aGuard).degree()==12
assert Sout/Sout.leading_coefficient()==(aGuard/aGuard.leading_coefficient())**3*(sGuard126/sGuard126.leading_coefficient())*(sGuard198/sGuard198.leading_coefficient())
assert all((Aout*Sout).gcd(f).degree()==0 for f in main.values())
assert Dout.gcd(main[144]).degree()==144 and Lout.gcd(main[36]).degree()==36
assert Dout.gcd(main[36]).degree()==Lout.gcd(main[144]).degree()==0
say('exact generic factors',1836,144,36,'and separately checked guards',12,36,36)
arrays=[t.cs for t in (A,B,C,sNorm,Nd,Nl,nReduced)]
