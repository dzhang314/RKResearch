"""Exact D projection for six zeros, three off clocks, and late mate."""
import sys
from time import monotonic
clock=monotonic()
def now(*a):print(round(monotonic()-clock,2),*a,flush=True)
phase=sys.argv[1]
import sympy as S
from sympy.polys.rings import ring
u,v,z=S.symbols("u v z")
Q=u**3-3*u**2+S.Rational(3,4)*u+S.Rational(1,2)
H=v**2-2*v-1
red=lambda p:S.rem(S.rem(S.expand(p),Q,u),H,v)
basis=[u**i*v**j for i in range(3) for j in range(2)]
vec=lambda a:S.Matrix([S.Poly(a,u,v).coeff_monomial(e) for e in basis])
B=S.Matrix.hstack(*(vec(red((u+2*v)**k)) for k in range(6)))
M=B.inv()
ucoef=M*vec(u);vcoef=M*vec(v)
assert red(sum(c*(u+2*v)**i for i,c in enumerate(ucoef))-u)==0
assert red(sum(c*(u+2*v)**i for i,c in enumerate(vcoef))-v)==0
f=S.Poly(S.resultant(Q,H.subs(v,(z-u)/2),u),z).monic()
assert f.degree()==6 and f.is_irreducible and red(f.as_expr().subs(z,u+2*v))==0
K=S.QQ.algebraic_field((f,z));Z=K.unit
U=sum((K.convert(c)*Z**i for i,c in enumerate(ucoef)),K.zero)
V=sum((K.convert(c)*Z**i for i,c in enumerate(vcoef)),K.zero)
assert U+2*V==Z
C=lambda a,b=1:K.convert(S.Rational(a,b))


T,D=ring('D',K);RR,X=ring('X',T.to_domain())
x=lambda a:RR(T(a))
a=1+2*U
s=D-1-(2*V if phase=='arith' else 2-V)
t=D-1-V
off=D-1
W=(2*V if phase=='arith' else 2-V)
p=(2*W*V+1+2*W-W*W)/(2*V)
P3=(X-x(a))*(X-x(s))*(X-x(t))
def I(P,k=D):
 return sum((c*k**j*C(1,j+1) for (j,),c in P.items()),T.zero)
m=[I(P3*X**j) for j in range(5)]
R0=x(p)*(P3//(X-x(s)))-x(V)*(P3//(X-x(t)))
r=[I(R0*X**i) for i in range(4)]
def det(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
M=[[m[0],m[1],m[2]],[m[1],m[2],m[3]],[r[0],r[1],r[2]]]
delta=det(M)
rhs=[-m[3],-m[4],-r[3]]
ns=[]
for j in range(3):
    MM=[z[:] for z in M]
    for i in range(3):MM[i][j]=rhs[i]
    ns.append(det(MM))
G=delta
for n in ns:G=G.gcd(n)
def L(T0):return 70*T0**4-140*D*T0**3+90*D*D*T0*T0-20*D**3*T0+D**4
guards=[D,s-a,t-a,off-1,off-1-U,L(T(a))]
def strip(p,guards):
 for g in guards:
  while True:
   h=p.gcd(g)
   if h.degree()==0:break
   p=p//h
 return p
GG=strip(G,guards)
now('singular coefficient projection gcd, guarded',G.degree(),GG.degree())
now('delta factors',[(h.degree(),i) for h,i in delta.factor_list()[1]])
now('singular coefficient factors',[(h.degree(),i) for h,i in GG.factor_list()[1]])
assert GG.degree()==0
q0,q1,q2=ns
Q=X**3+x(q2)*X**2+x(q1*delta)*X+x(q0*delta*delta)
AP=(X-x(T(a)*delta))*(X-x(s*delta))*(X-x(t*delta))*Q
# Cardinal numerator as polynomial in the label variable X.
Dcap=D*delta
B=RR.zero
for (ell,),c in AP.items():
    for j in range(ell):
        B+=x(c*Dcap**(ell-1-j)*C(1,ell-j))*X**j
Rback=(X-x(s*delta))*(X-x(t*delta))
J0=sum((x(c*C(1,n+1))*X**(n+1) for (n,),c in Rback.items()),RR.zero)
H0=J0.evaluate(X,Dcap)
W0=H0-J0.evaluate(X,t*delta)
BT=B.evaluate(X,t*delta)
F=(x(delta)*Rback-(x(H0)-J0))*B+x(W0*BT)
assert W0
F=F%Q
def Norm(z):
     C=[z*X**j%Q for j in range(3)]
     return det([[v.get((i,),T.zero) for i in range(3)] for v in C])
NF=Norm(F)
now('raw norm',NF.degree())

qk=q2; ql=q1*delta; qn=q0*delta*delta
disc=qk*qk*ql*ql-4*ql**3-4*qk**3*qn-27*qn*qn+18*qk*ql*qn
NF=strip(NF,guards+[delta,disc,Q.evaluate(X,T(a)*delta),Q.evaluate(X,s*delta),Q.evaluate(X,t*delta),
                     B.evaluate(X,s*delta),B.evaluate(X,t*delta)])
now('guarded norm degree',NF.degree())
fac=NF.factor_list()[1]
now('factors',[(h.degree(),m) for h,m in fac])
assert [(h.degree(),m) for h,m in fac]==[(14 if phase=='star' else 18,1)]

from flint import nmod_poly
from sympy import primerange
def seek(phi):
  def cmod(c,p):
     c=S.Rational(str(c));return int(c.p)*pow(int(c.q),-1,p)%p
  def smod(q,z0,p):
     h=0
     for c in q.to_list():h=(h*z0+cmod(c,p))%p
     return h
  def poly(q,z0,p):
     return nmod_poly([smod(q.get((k,),K.zero),z0,p) for k in range(q.degree()+1)],p) if q else nmod_poly([],p)
  for pp in primerange(11,500):
   zpoly=nmod_poly([cmod(c,pp) for c in reversed(f.all_coeffs())],pp)
   for zz0,ee in zpoly.roots():
    if ee!=1:continue
    zz=int(zz0)
    try:
     gg=poly(phi,zz,pp)
    except ValueError:
     continue
    if gg.degree()!=phi.degree():continue
    for DD0,ee in gg.roots():
     if ee!=1:continue
     DD=int(DD0);uu=smod(U,zz,pp);vv=smod(V,zz,pp)
     try:
      dd=int(poly(delta,zz,pp)(DD))
      if not DD or not dd:continue
      QQ=[int(poly(n,zz,pp)(DD))*pow(dd,-1,pp)%pp for n in ns]+[1]
     except ValueError:
      continue
     X=nmod_poly([0,1],pp)
     qa=nmod_poly(QQ,pp)
     aa=(1+2*uu)%pp;ss=(DD-1-(2*vv if phase=='arith' else 2-vv))%pp;tt=(DD-1-vv)%pp
     if len({aa,ss,tt})<3 or any(qa(x)==0 for x in (aa,ss,tt)) or qa.gcd(qa.derivative()).degree()>0:continue
     pn=(X-aa)*(X-ss)*(X-tt)*qa
     def Ihat(i):return pow(DD,i,pp)*pow(i+1,-1,pp)%pp
     BM=nmod_poly([],pp)
     for k in range(1,pn.degree()+1):
      for i in range(k):BM+=int(pn[k])*Ihat(k-1-i)*X**i
     def J(P,j=0):
      return nmod_poly([0]*(j+1)+[int(P[i])*pow(i+j+1,-1,pp)%pp for i in range(P.degree()+1)],pp)
     def Rprim(P):
      W=J(P)
      return int(W(DD))-W
     Rb=(X-ss)*(X-tt);Jb=Rprim(Rb)
     Fr=(Rb-Jb)*BM+int(Jb(tt))*int(BM(tt))
     h=qa.gcd(Fr)
     if h.degree()!=1:continue
     rr=int(h.roots()[0][0])
     QB=qa//(X-rr)
     if QB.degree()!=2:continue
     b=X;c=(-int(QB[1])-X)%QB
     def ev(F,x):
      if isinstance(x,int):return nmod_poly([int(F(x))],pp)
      q=nmod_poly([],pp)
      for j in range(F.degree(),-1,-1):q=(q*x+int(F[j]))%QB
      return q
     L=70*X**4-140*DD*X**3+90*DD*DD*X*X-20*DD**3*X+DD**4
     Pf=2*X-1-pow(2,-1,pp)*X*X
     Rf=(X-1)*(X-(1+uu))
     def G(P):
      return (int(L(aa))*(aa*(J(P)-P)+X*P-J(P,1))-L*(aa*int(P(aa))-int(J(P,1)(aa))))%QB
     z0,z1=G(Pf),G(Rf)
     def p_hat(x):return (z1*ev(Pf,x)-z0*ev(Rf,x))%QB
     R3=(X-1)*(X-(1+uu))*(X-(DD-1))
     pa=p_hat(aa);pb=p_hat(b)
     def wp(x):
      x0=nmod_poly([x],pp) if isinstance(x,int) else x
      return (pa*pb*(b-aa)*ev(R3,x)-p_hat(x)*(pb*int(R3(aa))*(b-x0)+pa*ev(R3,b)*(x0-aa)))%QB
     assert not wp(aa) and not wp(b)
     S3=(X-ss)*(X-tt)*(X-rr)
     PS=Rprim(S3)
     Pp=pn.derivative()
     def weight(x):
      return int(BM(x))*pow(int(Pp(x)),-1,pp)%pp
     test=nmod_poly([],pp)
     for x in (ss,tt,rr):test=(test-weight(x)*wp(x)*int(PS(x)))%QB
     h0,iv,_=ev(Pp,c).xgcd(QB)
     assert h0==nmod_poly([1],pp)
     test=(test+ev(BM,c)*iv*wp(c)*(ev(S3,c)-ev(PS,c)))%QB
     if test.gcd(QB).degree()==0:
       now('fourth reverse exact obstruction modulo',pp,'primitive',zz,'u,v,D,r:',uu,vv,DD,rr)
       return [pp,zz,uu,vv,DD,rr]
  return None
for h,e in fac:
 now('factor degree',h.degree(),'multiplicity',e)
 rr=seek(h.monic())
 now('good reduction proof',rr)
 assert rr==([89,87,35,26,62,54] if phase=="star" else [31,22,5,24,11,16])
