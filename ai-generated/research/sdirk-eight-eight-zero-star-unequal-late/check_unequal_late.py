"""Exact exclusion of both late-early mates of the unequal-cardinal paired star."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
assert Q.is_irreducible
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
K=E;z=w;G=F
u=ev(K,u_w,w);b=ev(K,b_w,w)
assert u+b==z
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
def stripC2(poly):
 while poly.degree()>0:
  d=poly.gcd(l2)
  if d.degree()==0:break
  poly=poly//d
 return poly




P,T=ring('T',R.to_domain())
co=lambda z:P(R(z))
Z3T=(T-co(a))*(T-co(b))*(T-co(X))
s=D-1;m=D-2
def I1(P):
    return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def red_field(L,t):
    return sum((q*D**i*t**j for (i,j),q in L.items()),R.zero)
uT=((Z3-J3)*J2b-(Z2-J2)*J3b)/R(dj)
vT=((Z2-J2)*J3a-(Z3-J3)*J2a)/R(dj)
LL=[R.one,2*X-D,6*X**2-6*D*X+D**2,20*X**3-30*D*X**2+12*D**2*X-D**3]
L4=L(X)
def de(L):
    q,rm=divmod(L-uT*red_field(L,a)-vT*red_field(L,b),Z2)
    assert not rm
    return q
G3=[de(L) for L in LL]
RR,V=ring('v',R.to_domain())
cv=lambda z:RR(R(z))
Y=V+cv(m)
def atQ(G):
    return sum((cv(h*D**i)*Y**j for (i,j),h in G.items()),RR.zero)
GK=sum((cv((2*j+1)*D**(6-2*j)*G3[j])*atQ(LL[j]) for j in range(4)),RR.zero)
now('GK',GK.degree())
mm=[cv(I1(Z3T*(T-co(m))**j)) for j in range(5)]
A=[mm[j+3]-mm[j+2]-V**2*(mm[j+1]-mm[j]) for j in range(2)]
B=[mm[j+3]-2*mm[j+1]-V*(mm[j+2]-2*mm[j]) for j in range(2)]
AB=A[0]*B[1]-A[1]*B[0]
now('AB degree in gap',AB.degree())
def de2(rs):
    if not rs: return ('zero',)
    return (rs.degree(D),rs.degree(X),len(rs.terms()))
now('coeff degrees', [de2(v) for m,v in GK.terms()],[de2(v) for m,v in AB.terms()])
P0=GK.resultant(AB)
now('inner resultant degrees',de2(P0))
Dexp=R.from_dict({(i,j):v for (i,j),v in P0.items()})
assert Dexp==P0
def asD(p):
    return D1.from_dict({(i,):z for (i,j),z in p.items()})
def strip_linear(p,s):
    n=0
    while p.degree()>0:
        a,b=divmod(p,s)
        if b:break
        p=a;n+=1
    return p,n
def nrm_pair(poly):
    j=poly.degree(X)
    pp,qq=D1.zero,D1.zero
    z,w=D1.one,D1.zero
    for i in range(j+1):
        f=ccollect(poly,i)*l2**(j-i)
        pp+=f*z;qq+=f*w
        z,w=pair_times((z,w),(D1.zero,D1.one))
    return pp,qq
def pairnorm(a,b):
    return a*a-a*b*l1+b*b*l2*l0
an,bn=nrm_pair(P0)
now('norm pair',an.degree(),bn.degree())
nr0=pairnorm(an,bn)
now('raw norm degree',nr0.degree())
Nr=stripC2(nr0)
now('leading guard stripped norm degree',Nr.degree())
for g in [DD]+list(map(asD,[s-a,s-b])):
    Nr,n=strip_linear(Nr,g)
    now('scalar guard removed',n)
now('guarded norm degree',Nr.degree())
assert nr0.degree()==186 and Nr.degree()==114
L5=252*X**5-630*D*X**4+560*D**2*X**3-210*D**3*X**2+30*D**4*X-D**5
p43=red_field(L4,a)*red_field(LL[3],b)-red_field(L4,b)*red_field(LL[3],a)
p45=red_field(L4,a)*red_field(L5,b)-red_field(L4,b)*red_field(L5,a)
E0,E1=nrm_pair(p45*G3[3]-p43*de(L5))
rank=stripC2(pairnorm(E0,E1))
assert rank.degree()==30
N,rem=divmod(Nr,rank**2)
assert not rem and N.degree()==54
# The exact complementary factor is a cube: recover its proposed monic
# root by reverse leading coefficients, and verify by multiplication back.
def cube_root(poly):
    pol=poly.monic()
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
assert N.degree()==18
S0,S1,S2,S3,S4=[h.get((0,),R.zero) for h in mm]
HS=S0*(S2*S4-S3*S3)-S1*(S1*S4-S2*S3)+S2*(S1*S3-S2*S2)
h0,h1=nrm_pair(HS)
assert not ((h0%rank)*(bn%rank)-(h1%rank)*(an%rank))%rank
now('exact square-cube split and Hankel branch',rank.degree(),N.degree())


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
    nr=specialize(N,p,z0); hr=specialize(rank,p,z0)
    n2=specialize(l2,p,z0); n1=specialize(l1,p,z0); n0=specialize(l0,p,z0)
    na,nb=[specialize(a,p,z0,False) for a in (an,bn)]
    assert nr.gcd(hr).degree()==0
    assert all(nd.gcd(q).degree()==0 for nd in (nr,hr) for q in (n2,nb))
    assert n2.gcd(n1).degree()==0
    for branch,poly,degs in [('rank',hr,[1,5,24]),('regular',nr,[1,3,5,9]),('drop',n2,[4])]:
      answers=[]
      factors=poly.factor()[1]
      assert sorted(f.degree() for f,m in factors)==degs and all(m==1 for f,m in factors)
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
            mm0,mm1,mm2,mm3,mm4=[C(h.get((0,),R.zero)) for h in mm]
            assert C(HS).is_zero() and not Dq.is_zero()
            Delta=mm0*mm2-mm1**2
            assert not Delta.is_zero()
            u=(mm1*mm3-mm2**2)/Delta
            v=(mm1*mm2-mm0*mm3)/Delta
            Q2=Z**2+v*Z+u
            assert H==Q2
            assert (gpol//Q2).gcd(apol//Q2).degree()==0
            answers.append((f.degree(),"Hankel two-atom"))
            continue
        if H.degree()==0:
            answers.append((f.degree(),"no common gap"))
            continue
        # Work in the entire common gap quotient (possibly nonsplit).
        A0,A1,B0,B1=[Pq([C(r.get((j,),R.zero)) for j in range(4)])%H for r in (*A,*B)]
        m0,m1,m2=[C(mm[j].get((0,),R.zero)) for j in range(3)]
        m=Dq-2;s=Dq-1; q=(Z+m)%H
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
        u0,u1=Qq*(m1-m0)+fK*Dq**6*(Z-1),Qq*(m2-m1)+fK*Dq**6*(Z-1)*Z
        H1=H.gcd(A0*u1-A1*u0).gcd(B0*u1-B1*u0)
        assert H0.degree()==H1.degree()==0
        answers.append((f.degree(),H.degree(),"both fourth reads excluded"))
      print('fibre census',branch,answers,flush=True)


p,z0=17,11
assert S.isprime(p) and p>7
check_fibers(p,z0)
