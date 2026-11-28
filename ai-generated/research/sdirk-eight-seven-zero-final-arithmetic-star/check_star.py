"""Division-free polynomial ordered-root norm in the final reflected-star chart."""
from flint import fmpq_poly as p, fmpq, nmod_poly, fq_default_ctx, fq_default_poly_ctx
from time import monotonic
from itertools import permutations
import sympy as Sym
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
A=1680*g**4-840*g**3+180*g*g-20*g+1
B=-6720*g**4+4200*g**3-1080*g*g+140*g-8
C=2520*g**4-1680*g**3+540*g*g-120*g+11
E=Alg([A*C,B],None);e=E.gen()
# Inverse Hilbert 4×4 entry rows are explicit.
Hinv=[[16,-120,240,-140],[-120,1200,-2700,1680],[240,-2700,6480,-4200],[-140,1680,-4200,2800]]
mom=[p([1]),g,2*g*g,6*g**3]
S=[sum((row[j]*mom[j] for j in range(4)),p()) for row in Hinv]
L=[p([fmpq(1,70)]),p([fmpq(-2,7)]),p([fmpq(9,7)]),p([-2]),p([1])]
gE=E.co(g)
g_e=gE*e
Ss=sum((E.co(S[i]*A**(3-i))*g_e**i for i in range(4)),E.co(0))
Ls=sum((E.co(L[i]*A**(4-i))*g_e**i for i in range(5)),E.co(0))
scale=E.co(A)*Ss
sNorm=norm2(Ss)
assert sNorm.degree()==36
say('scale norm',sNorm.degree())
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
assert nE.degree()==8868
say('raw norm degree',nE.degree())

F4=Alg(poly4,E);x=F4.gen()
dr=sum((F4.co(poly4[i])*i*x**(i-1) for i in range(1,4)),F4.co(0))+4*x**3
M=[(dr*x**i).cs for i in range(4)]
disc=E.co(0)
for perm in permutations(range(4)):
 sign=(-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
 term=E.co(sign)
 for i in range(4):
   term*=M[i][perm[i]]
 disc+=term
Nd=norm2(disc);Nl=norm2(Ls)
say('exact discard norms',Nd.degree(),Nl.degree())

def mod(f,p0):
    return nmod_poly([int(c.numerator)*pow(int(c.denominator),-1,p0)%p0 for c in f.coeffs()],p0)

a_factors=A.factor()[1]
assert len(a_factors)==1 and a_factors[0][0].degree()==4 and a_factors[0][1]==1
a_factor=A/A.leading_coefficient()
s_factors=[f/f.leading_coefficient() for f,e in sNorm.factor()[1] if f.degree()==12 and e==1]
assert len(s_factors)==2
s99,s76=[next(f for f in s_factors if mod(f,101)(j)==0) for j in (99,76)]
assert s99!=s76 and sNorm/sNorm.leading_coefficient()==a_factor**3*s99*s76
scaling=g**48*a_factor**990*s99**198*s76**126
reduced,rem=divmod(nE,scaling)
assert not rem and reduced.degree()==972
main_result={f.degree():f/f.leading_coefficient() for f,m in reduced.factor()[1]}
assert sorted((f.degree(),m) for f,m in reduced.factor()[1])==[(12,18),(48,3),(612,1)]
assert Nd.gcd(main_result[48]).degree()==48
assert Nl.gcd(main_result[12]).degree()==12
assert all((A*sNorm).gcd(f).degree()==0 for f in main_result.values())
say('exact generic factors',612,48,12,'and separate guards',4,12,12)

# Check the plane equation used for the monic e tower directly.
gx,ex,x=Sym.symbols('gamma e x')
sq=[sum(w[j]*gx**j*Sym.factorial(j) for j in range(4)) for w in Hinv]
ll=[Sym.Rational(1,70),-Sym.Rational(2,7),Sym.Rational(9,7),-2,1]
z=gx*ex
def ev(cs,x):
    return sum(c*x**j for j,c in enumerate(cs))
def cm(cs,x):
    return sum(c*x**i/Sym.Integer(j-i) for j,c in enumerate(cs) for i in range(j))
FF=z**3-9*gx*z*z+18*gx*gx*z-6*gx**3
WW=z*z-8*gx*z+11*gx*gx
det=ev(ll,z)*(FF*cm(sq,z)+WW)-ev(sq,z)*FF*cm(ll,z)
A0=1680*gx**4-840*gx**3+180*gx*gx-20*gx+1
B0=-6720*gx**4+4200*gx**3-1080*gx*gx+140*gx-8
C0=2520*gx**4-1680*gx**3+540*gx*gx-120*gx+11
assert Sym.expand(70*det-gx*gx*(A0*ex*ex+B0*ex+C0))==0
def test(g,Fq,P,cause):
 z=Fq(0);one=Fq(1)
 if g==z:return None
 A=1680*g**4-840*g**3+180*g*g-20*g+1
 B=-6720*g**4+4200*g**3-1080*g*g+140*g-8
 C=2520*g**4-1680*g**3+540*g*g-120*g+11
 x=P([0,1]);eg=A*x*x+B*x+C
 if cause=='a':
    if A!=z or B==z:return None
    es=[(-C/B,1)]
 else:
    if A==z:return None
    es=eg.roots()
    if len(es)!=2 or any(m!=1 for _,m in es):return None
 skipped=0
 moment=[one,g,2*g*g,6*g**3]
 S=[sum((Fq(w[j])*moment[j] for j in range(4)),z) for w in Hinv]
 L=[one/70,-Fq(2)/7,Fq(9)/7,-Fq(2),one]
 ls=P(L);ss=P(S)
 def cm(p,e):
   return sum((c*e**i/Fq(j-i) for j,c in enumerate(p) for i in range(j)),z)
 bad=[]
 stats=[0,0,0]
 for e,_ in es:
    t=g*e
    fv=t**3-9*g*t*t+18*g*g*t-6*g**3
    wv=t*t-8*g*t+11*g*g
    pivot=fv*cm(S,t)+wv
    const=fv*cm(L,t)
    if ss(t)!=z:
        q=-(ls(t)/ss(t))
        if const+pivot*q!=z:continue
    elif cause in ('a','s') and pivot!=z:
        q=-const/pivot
        if ls(t)!=z:continue
    elif cause=='s' and sum(ss(g*k)==z for k,_ in es)==1 and ls(t)!=z:
        # Exact S-norm zero, with a unique matching residue branch.
        continue
    else:return None
    if q==z:
        if cause=='zero':skipped+=1;continue
        return None
    p4=ls+q*ss
    rr=p4.roots()
    if sum(m for _,m in rr)!=4:return None
    if len(rr)!=4 or any(m!=1 for _,m in rr):
        if cause=='disc':skipped+=1;continue
        return None
    assert t in [j for j,_ in rr]
    pp=[one-a for a,m in rr if a!=t]
    assert len(pp)==3
    U=x;H=-2+U+4*U*U-U**3
    p0=[-g*g,2*g,-one/2]
    p1=[g*g,-2*g,one];p2=[g*g,-g,z]
    ps=[H*p0[i]+(3*U-2)*(p1[i]+U*p2[i]) for i in range(3)]
    ds=[P([g]),g*(1+U),g*(1+2*U)]
    r0,r1,r2=ds
    rs=[-r0*r1*r2,r0*r1+r0*r2+r1*r2,-r0-r1-r2,P([1])]
    def v(ar,t):return sum((c*t**j for j,c in enumerate(ar)),P([]))
    def jv(ar,t,k=0):return sum((c*t**(i+k+1)/Fq(i+k+1) for i,c in enumerate(ar)),P([]))
    def L4(t):return 70*t**4-140*t**3+90*t*t-20*t+1
    for a,b,c in permutations(pp):
        la,lb,lc=L4(a),L4(b),L4(c)
        pa,pb,pc=[v(ps,t) for t in (a,b,c)]
        ra,rb,rc=[v(rs,t) for t in (a,b,c)]
        ja,jb,jc=[jv(ps,t) for t in (a,b,c)]
        jta,jtb,jtc=[jv(ps,t,1) for t in (a,b,c)]
        jra,jrb,jrc=[jv(rs,t) for t in (a,b,c)]
        q0=ja-g*pa
        q1=la*(g*(b-a)*pb+a*jb-jtb)-lb*(g*a*pa-jta)
        q2=la*(pa*(g*rb-jrb)+(jb-g*pb)*ra)-lb*pa*(g*ra-jra)
        if max(q0.degree(),q1.degree())!=3:return None
        stats[0]+=1
        cmn=q0.gcd(q1)
        if not cmn.degree():continue
        cmn=cmn.gcd(q2)
        stats[1]+=1
        if not cmn.degree():continue
        stats[2]+=1
        lc1=la*(jtc-g*c*pc)+(g*a*pa-jta)*lc
        lc2=la*(jrc-g*rc)+(g*ra-jra)*lc
        q3=pa*(la*b*pb*lc2-lc1*la*rb)-pb*(la*a*pa*lc2-lc1*la*ra)+(jc-g*pc)*(la*a*pa*la*rb-la*b*pb*la*ra)
        cmn=cmn.gcd(q3)
        if cmn.degree():bad.append(str(cmn))
 if skipped!=(1 if cause in ('disc','zero') else 0):return None
 return stats,bad


CERTS=(
    (main_result[612],101,[35,95,1],None,[12,1,0]),
    (main_result[48],103,[85,1],'disc',[6,0,0]),
    (main_result[12],101,[33,78,93,1],'zero',[6,0,0]),
    (a_factor,101,[11,1],'a',[6,0,0]),
    (s99,101,[2,1],'s',[12,0,0]),
    (s76,101,[25,1],'s',[6,0,0]),
)
for ff,p0,loc,why,expected in CERTS:
    assert Sym.isprime(p0)
    pf=mod(ff,p0)
    lf=nmod_poly(loc,p0)
    assert pf.degree()==ff.degree() and pf%lf==0 and pf.derivative().gcd(lf).degree()==0
    assert len(lf.factor()[1])==1 and lf.factor()[1][0][0].degree()==lf.degree() and lf.factor()[1][0][1]==1
    h=lf.degree()
    Fq=fq_default_ctx(p0,12*h,var='a'); P=fq_default_poly_ctx(Fq)
    assert Fq.modulus().is_irreducible()
    roots=P(loc).roots()
    assert len(roots)==h and all(e==1 for _,e in roots)
    for gamma,_ in roots:
        st,bad=test(gamma,Fq,P,why)
        assert st==expected and not bad
    say('checked',ff.degree(),why,p0,loc,'front tests',expected)
