"""Three off clocks, one active pair, physical first zero 4 and star front."""
import sys
from time import monotonic
clock=monotonic()
def now(*a):print(round(monotonic()-clock,2),*a,flush=True)
phase=sys.argv[1]
import sympy as S
from sympy.polys.rings import ring
u,v,z=S.symbols("u v z")
Q=u**3-9*u**2+18*u-6
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
a=U
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
guards=[D,s-a,t-a,L(T(a))]
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
if GG.degree()>0:print("SINGULAR NEEDS CHECK",GG.as_expr(),flush=True)
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


GG=delta
for n in ns:GG=GG.gcd(n)
assert strip(GG,guards).degree()==0
a0=x(T(a)*delta)
b=X
P=[-x(delta*delta),2*x(delta),x(C(-1,2))]
def ev(z):return sum((p*z**i for i,p in enumerate(P)),RR.zero)
def J(k,z):return sum((p*x(C(1,i+k+1))*z**(i+k+1) for i,p in enumerate(P)),RR.zero)
def LL(z):return 70*z**4-140*x(Dcap)*z**3+90*x(Dcap**2)*z*z-20*x(Dcap**3)*z+x(Dcap**4)
F2=LL(a0)*(a0*(J(0,b)-x(delta)*ev(b))+x(delta)*b*ev(b)-J(1,b))-LL(b)*(x(delta)*a0*ev(a0)-J(1,a0))
F2=F2%Q
NN=Norm(F2)
more=[delta,disc,Q.evaluate(X,T(a)*delta),Q.evaluate(X,s*delta),Q.evaluate(X,t*delta),B.evaluate(X,s*delta),B.evaluate(X,t*delta)]
NG=strip(NN,guards+more)
fg=NG.gcd(NF)
now('forward projected degree',NG.degree(),'common',fg.degree(),[(p.degree(),i) for p,i in fg.factor_list()[1]])
assert fg.degree()==0
