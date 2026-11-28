"""Fixed exact ghost/arithmetic exclusion for either late onsite affine root."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('ghost','arith')
vdegree=3 if kind=='ghost' else 6
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv=(v_**3-4*v_**2-v_+2 if kind=='ghost' else
    (8*v_**6-44*v_**5+22*v_**4+97*v_**3-55*v_**2-13*v_+6))
H=S.Poly(Hv,v_).monic()
assert Q.is_irreducible and H.is_irreducible
K=S.QQ.algebraic_field((Q,u_));u=K.unit
R,b=ring('b',K)
Bb=b*b-(2*u+4)*b+1+2*u
F=S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,w_-u_),u_),w_).monic()
assert F.degree()==6 and F.is_irreducible


def recover(K,R,t,mod,f,aa,bb,n,m):
    def vec(p):
        return S.Matrix([S.Rational(str((p.get((j,),K.zero).to_list()[::-1]+[0]*n)[i]))
                         for j in range(m) for i in range(n)])
    C=S.Matrix.hstack(*(vec(t**i%mod) for i in range(n*m)))
    C=C.inv()
    a=C*vec(aa);b=C*vec(bb)
    def eval(z):
        return sum((R(K.convert(x))*t**i%mod for i,x in enumerate(z)),R.zero)%mod
    assert eval(a)==aa and eval(b)==bb and not eval(f.all_coeffs()[::-1])
    return a,b
u_w,b_w=recover(K,R,R(u)+b,Bb,F,R(u),b,3,2)
E=S.QQ.algebraic_field((F,w_));w=E.unit
def ev(field,P,y):
    return sum((field.convert(x)*y**i for i,x in enumerate(P)),field.zero)
G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
assert G.degree()==6*vdegree and G.is_irreducible
S0,v=ring('v',E)
VH=sum((E.convert(x)*v**j for j,x in enumerate(H.all_coeffs()[::-1])),S0.zero)
w_z,v_z=recover(E,S0,S0(w)+2*v,VH,G,S0(w),v,6,vdegree)
K=S.QQ.algebraic_field((G,z_));z=K.unit
w=ev(K,w_z,z);v=ev(K,v_z,z);u=ev(K,u_w,w);b=ev(K,b_w,w)
assert u+b+2*v==z and not ev(K,H.all_coeffs()[::-1],v)
a=1+2*u
assert a and b and a!=b
assert not (4*u**3-12*u*u+3*u+2) and not (b*b-(2*u+4)*b+1+2*u)
now('primitive degree',G.degree())

C=lambda q,r=1:K.convert(S.Rational(q,r))
R,D,X=ring('D X',K)
I=lambda p:sum((q*C(1,j+1)*D**(i+j) for (i,j),q in p.items()),R.zero)

Z2=(X-a)*(X-b); Z3=X*Z2
J=lambda P:sum((c*C(1,j+1)*D**i*X**(j+1) for (i,j),c in P.items()),R.zero)
J2,J3=J(Z2),J(Z3)
def ex(p,x):return sum((c*x**j for (i,j),c in p.items()),K.zero)
J2a,J2b=ex(J2,a),ex(J2,b);J3a,J3b=ex(J3,a),ex(J3,b)
dj=J2a*J3b-J2b*J3a
assert dj==a*a*b*b*(a-b)**3*C(1,24) and dj
L=lambda x:70*x**4-140*D*x**3+90*D**2*x*x-20*D**3*x+D**4
ap=(-L(a)*J3b+L(b)*J3a)/R(dj)
bp=(-J2a*L(b)+J2b*L(a))/R(dj)
CC,rem=divmod(ap*(Z2-J2)+bp*(Z3-J3)-L(X),Z2)
assert not rem and CC.degree(X)==2
def evX(p,y):return sum((c*D**i*y**j for (i,j),c in p.items()),R.zero)
D1,DD=ring('q',K)
def ccollect(G,j):
 return D1.from_dict({(i,):z for (i,d),z in G.items() if d==j})
l0,l1,l2=[ccollect(CC,i) for i in range(3)]
def pair_times(x,y):
 a,b=x;c,d=y
 return a*c-b*d*l2*l0,a*d+b*c-b*d*l1
def nrm(poly):
 j=poly.degree(X)
 ps=[(D1.one,D1.zero)]
 for i in range(j):
  ps.append(pair_times(ps[-1],(D1.zero,D1.one)))
 a,b=D1.zero,D1.zero
 for i in range(j+1):
   z=ccollect(poly,i)*l2**(j-i)
   a+=z*ps[i][0];b+=z*ps[i][1]
 return a*a-a*b*l1+b*b*l2*l0

# Field inverses are done with FLINT polynomial extended gcd, once per divisor.
# Repeated SymPy ANP inversions of the same leading coefficient can blow up.
from flint import fmpq_poly, fmpq
from functools import lru_cache
fld=fmpq_poly([fmpq(str(x)) for x in reversed(G.all_coeffs())])
@lru_cache(None)
def inv_coeff(vals):
    raw=fmpq_poly([fmpq(str(x)) for x in vals[::-1]])
    g,s,t=raw.xgcd(fld)
    assert g.degree()==0
    v=s/g[0]
    return K.dtype(list(reversed(v.coeffs())),K.mod,K.dom)
def div_safe(f,g):
    assert g and f.ring==D1 and g.ring==D1
    m,n=f.degree(),g.degree()
    if m<n:return D1.zero,f
    leading=inv_coeff(tuple(g.LC.to_list()))
    gg=[g.get((i,),K.zero)*leading for i in range(n+1)]
    assert gg[-1]==K.one and leading*g.LC==K.one
    front=[f.get((i,),K.zero) for i in range(m+1)]
    qu=[K.zero]*(m-n+1)
    for j in range(m-n,-1,-1):
        z=front[j+n]
        qu[j]=z*leading
        for i,k in enumerate(gg[:-1]):front[j+i]-=z*k
    return (D1.from_dict({(i,):z for i,z in enumerate(qu) if z}),
            D1.from_dict({(i,):z for i,z in enumerate(front[:n]) if z}))
def small_gcd(f,g):
    while g:
        _,r=div_safe(f,g)
        f,g=g,r
    return f
def stripC2(poly):
    if not poly:return poly
    while poly.degree()>0:
        d=small_gcd(poly,l2)
        if d.degree()==0:break
        poly,rem=div_safe(poly,d)
        assert not rem
    return poly


P,T=ring('T',R.to_domain())
co=lambda z:P(R(z))
sigma=(T-co(a))*(T-co(b))*(T-co(X))
s=D-1;m=s-v
def I1(P):
    return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def red_field(L,t):
    return sum((q*D**i*t**j for (i,j),q in L.items()),R.zero)
alpha=((Z3-J3)*J2b-(Z2-J2)*J3b)/R(dj)
beta=((Z2-J2)*J3a-(Z3-J3)*J2a)/R(dj)
LL=[R.one,2*X-D,6*X**2-6*D*X+D**2,20*X**3-30*D*X**2+12*D**2*X-D**3]
L4=L(X)
def de(L):
    q,rm=divmod(L-alpha*red_field(L,a)-beta*red_field(L,b),Z2)
    assert not rm
    return q
G3=[de(L) for L in LL]
RR,Z=ring('delta',R.to_domain())
cv=lambda z:RR(R(z))
Yq=Z+cv(m)
def atQ(G):
    return sum((cv(h*D**i)*Yq**j for (i,j),h in G.items()),RR.zero)
GK=sum((cv((2*j+1)*D**(6-2*j)*G3[j])*atQ(LL[j]) for j in range(4)),RR.zero)
MM=[I1(sigma*(T-co(m))**j) for j in range(5)]
mm=[cv(h) for h in MM]
kap=1+2*v-v*v
H0=v**3-4*v*v-v+2
Q0=4*v**3-12*v*v+3*v+2
N1=[-cv(kap*v*v)*(cv(v)-Z),cv(v)*Z,cv(kap)*(cv(v)-Z)+Z]
N2=[cv(0),-cv(v),cv(1)] if kind=='ghost' else [
    cv(2*H0*kap*v*v),cv(v*(H0+kap*Q0)),cv(H0*(1-2*kap)-kap*Q0)]
def lines(row):
    return [sum((row[j]*(mm[i+j+1]-Z*mm[i+j]) for j in range(3)),RR.zero) for i in (0,1)]
A,B=lines(N1),lines(N2)
AB=A[0]*B[1]-A[1]*B[0]
assert AB.degree()==GK.degree()==3
now('gap cubic pair prepared')
def asD(p):
    return D1.from_dict({(i,):z for (i,j),z in p.items()})
def strip_factor(p,s):
    n=0
    while p.degree()>=s.degree():
        a,b=div_safe(p,s)
        if b:break
        p=a;n+=1
    return p,n
def nrm_pair(poly,scale=None):
    j=poly.degree(X) if scale is None else scale
    pp,qq=D1.zero,D1.zero
    z,w=D1.one,D1.zero
    for i in range(j+1):
        f=ccollect(poly,i)*l2**(j-i)
        pp+=f*z;qq+=f*w
        z,w=pair_times((z,w),(D1.zero,D1.one))
    return pp,qq
def pairnorm(a,b):
    return a*a-a*b*l1+b*b*l2*l0
ZERO=(D1.zero,D1.zero)
ONE=(D1.one,D1.zero)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
mul=pair_times
# Cubic Bezout matrix in the scaled monic C3 algebra, no C3 divisions.
PP=[nrm_pair(GK.get((j,),R.zero),2) for j in range(4)]
QQ=[nrm_pair(AB.get((j,),R.zero),2) for j in range(4)]
Bz=[[ZERO for _ in range(3)] for _ in range(3)]
for i in range(1,4):
    for j in range(i):
        el=sub(mul(PP[i],QQ[j]),mul(PP[j],QQ[i]))
        for k0 in range(i-j):
            d1,d2=i-1-k0,j+k0
            Bz[d1][d2]=add(Bz[d1][d2],el)
def det(A):
    m0=sub(mul(A[1][1],A[2][2]),mul(A[1][2],A[2][1]))
    m1=sub(mul(A[1][0],A[2][2]),mul(A[1][2],A[2][0]))
    m2=sub(mul(A[1][0],A[2][1]),mul(A[1][1],A[2][0]))
    return add(sub(mul(A[0][0],m0),mul(A[0][1],m1)),mul(A[0][2],m2))
an,bn=det(Bz)
now('Bezout pair degrees',an.degree(),bn.degree())
raw=pairnorm(an,bn)
now('raw diagonal degree',raw.degree())
assert raw.degree()==186
N,rem=div_safe(raw,l2**12)
assert not rem
N,drop=strip_factor(N,DD)
now('after exact L2/D saturation',drop,N.degree())
assert drop==24 and N.degree()==114
for g0 in [z-y for z in (s,m,m-v) for y in (a,b)]:
    N,dg=strip_factor(N,asD(g0))
    assert dg==0
now('base guarded degree',N.degree())
L5=252*X**5-630*D*X**4+560*D**2*X**3-210*D**3*X**2+30*D**4*X-D**5
p43=red_field(L4,a)*red_field(LL[3],b)-red_field(L4,b)*red_field(LL[3],a)
p45=red_field(L4,a)*red_field(L5,b)-red_field(L4,b)*red_field(L5,a)
E0,E1=nrm_pair(p45*G3[3]-p43*de(L5))
H,rm=div_safe(pairnorm(E0,E1),l2**3)
assert not rm and H.degree()==30
N,kH=strip_factor(N,H)
now('exact rank and remaining powers',kH,N.degree())
assert kH==2 and N.degree()==54
S0,S1,S2,S3,S4=MM
HS=S0*(S2*S4-S3*S3)-S1*(S1*S4-S2*S3)+S2*(S1*S3-S2*S2)
h0,h1=nrm_pair(HS)
Hr=lambda t:div_safe(t,H)[1]
assert not Hr(Hr(h0)*Hr(bn)-Hr(h1)*Hr(an))
now('actual Hankel rank branch')
def cube_root(poly):
    pol,rem=div_safe(poly,D1(poly.LC))
    assert not rem
    degree=pol.degree()
    assert degree%3==0
    n=degree//3
    cc=[K.one]
    for i in range(1,n+1):
        subtotal=sum((cc[j]*cc[k]*cc[i-j-k] for j in range(i) for k in range(i-j+1)
                     if k<i and i-j-k<i),K.zero)
        cc.append((pol.get((degree-i,),K.zero)-subtotal)*C(1,3))
    A=D1.from_dict({(n-i,):q for i,q in enumerate(cc)})
    assert A**3==pol
    return A
N=cube_root(N)
now('exact residual cube root degree',N.degree())
assert N.degree()==18


rank_factor=H
from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():n=(n*z0+rr(k,p))%p
    return n
def specialize(pol,p,z0,degree=True):
    q=nmod_poly([evk(pol.get((i,),K.zero),z0,p) for i in range(pol.degree()+1)],p)
    if degree and q.degree()!=pol.degree(): raise ValueError('lead drops')
    return q

def check_fibers(p,z0):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    assert gp(z0)==0 and gp.derivative()(z0)!=0
    nr=specialize(N,p,z0); hr=specialize(rank_factor,p,z0)
    n2=specialize(l2,p,z0); n1=specialize(l1,p,z0); n0=specialize(l0,p,z0)
    na,nb=[specialize(a,p,z0,False) for a in (an,bn)]
    assert nr.gcd(hr).degree()==0 and n2.gcd(n1).degree()==0
    assert all(nd.gcd(t).degree()==0 for nd in (nr,hr) for t in (n2,nb))
    vmod=evk(v,z0,p)
    for branch,poly in [('rank',hr),('regular',nr),('drop',n2)]:
      answers=[]
      factors=poly.factor()[1]
      expected={
          'ghost': {'rank':[1,5,24],'regular':[2,6,10],'drop':[4]},
          'arith': {'rank':[1,2,2,10,15],'regular':[1,17],'drop':[1,1,2]},
      }
      assert sorted(f.degree() for f,_ in factors)==expected[kind][branch]
      assert all(power==1 for _,power in factors)
      print('factor census',branch,[(f.degree(),i) for f,i in factors],flush=True)
      for f,power in factors:
        pp=fmpz_mod_poly_ctx(p)
        cq=fq_default_ctx(modulus=pp([int(o) for o in f.coeffs()]),var='D')
        Pq=fq_default_poly_ctx(cq)
        Dq=cq.gen()
        p1=cq.one()
        z=cq.zero()
        def ev(f):return Pq([int(x) for x in f.coeffs()])(Dq)
        def int2(x):
            return cq(int(x)%p)
        if branch!='drop': xc=-ev(na)/(ev(nb)*ev(n2))
        else: xc=-ev(n0)/ev(n1)
        assert (ev(n2)*xc**2+ev(n1)*xc+ev(n0)).is_zero()
        uK=lambda Kcoef: int2(evk(Kcoef,z0,p))
        C=lambda rr: sum((uK(t)*Dq**i*xc**j for (i,j),t in rr.items()),z)
        a0,b0=uK(a),uK(b)
        zero=Pq([]); one=Pq([p1]); Z=Pq([z,p1])
        gpol=Pq([C(GK.get((j,),R.zero)) for j in range(4)])
        apol=Pq([C(AB.get((j,),R.zero)) for j in range(4)])
        assert max(gpol.degree(),apol.degree())==3
        H=gpol.gcd(apol)
        if branch=='rank':
            mm0,mm1,mm2,mm3,mm4=list(map(C,MM))
            assert C(HS).is_zero() and not Dq.is_zero()
            Delta=mm0*mm2-mm1**2
            assert not Delta.is_zero()
            u=(mm1*mm3-mm2**2)/Delta
            qlinear=(mm1*mm2-mm0*mm3)/Delta
            Q2=Z**2+qlinear*Z+u
            assert H==Q2 and (gpol//Q2).gcd(apol//Q2).degree()==0
            answers.append((f.degree(),"Hankel two-atom"))
            continue
        if branch=='drop':
            assert H.degree()==0
            answers.append((f.degree(),"no common gap"))
            continue
        assert H.degree()==3
        # Work in the entire common gap quotient (possibly nonsplit).
        A0,A1,B0,B1=[Pq([C(r.get((j,),R.zero)) for j in range(4)])%H for r in (*A,*B)]
        n0m,n1m,n2m,n3m,n4m=list(map(C,MM))
        v0=cq(vmod)
        m=Dq-1-v0;s=Dq-1; q=(Z+m)%H
        L0=L1=L2=L3=z
        L=[one,2*Z-Dq,6*Z**2-6*Dq*Z+Dq**2,20*Z**3-30*Dq*Z**2+12*Dq**2*Z-Dq**3]
        L4=70*Z**4-140*Dq*Z**3+90*Dq**2*Z**2-20*Dq**3*Z+Dq**4
        K=[zero]*5
        for j,Lj in enumerate(L):
          h=(2*j+1)*Dq**(6-2*j)*Lj(q)%H
          for i,Tcoef in enumerate(Lj.coeffs()): K[i]=(K[i]+h*Tcoef)%H
        def e(lst,at):return sum((t*(at**i) for i,t in enumerate(lst)),zero)%H
        Ka,Kb=e(K,a0),e(K,b0)
        La,Lb=L4(a0),L4(b0)
        det=(La*Kb-Lb*Ka)%H
        S3=(Z-a0)*(Z-b0)*(Z-xc)
        J=Pq([z]+[t/cq(i+1) for i,t in enumerate(S3.coeffs())])
        fa,fb=-J(a0),-J(b0)
        f4=(fa*Kb-fb*Ka)%H; fK=(La*fb-Lb*fa)
        SJ=S3-J
        Sh=[(det*SJ[i]-f4*L4[i]-fK*K[i])%H for i in range(5)]
        LQ=[zero]*2
        for j in range(1,-1,-1):
          LQ[j]=Sh[j+3]
          for i,Scoef in enumerate(S3.coeffs()): Sh[j+i]=(Sh[j+i]-LQ[j]*Scoef)%H
        assert all(r.is_zero() for r in Sh)
        # q=e (fourth is a singleton)
        u0,u1=LQ[1],-LQ[0]-m*LQ[1]
        H0=H.gcd(A0*u1-A1*u0).gcd(B0*u1-B1*u0)
        # q=d (fourth is the repeated early copy, so the jump is present)
        Qq=(LQ[0]+q*LQ[1])%H
        mu0=n3m-v0**2*n1m; mu1=n4m-v0**2*n2m
        jt = fK*Dq**6*Z*(Z**2-v0**2)
        u0,u1=Qq*mu0+jt,Qq*mu1+jt*Z
        H1=H.gcd(A0*u1-A1*u0).gcd(B0*u1-B1*u0)
        assert H0.degree()==H1.degree()==0
        answers.append((f.degree(),H.degree(),"both fourth reads excluded"))
      print('fibre census',branch,answers,flush=True)


p,z0={'ghost':(17,6),'arith':(103,65)}[kind]
assert p>7 and S.isprime(p)
check_fibers(p,z0)
print("verified",kind,p,z0,flush=True)
