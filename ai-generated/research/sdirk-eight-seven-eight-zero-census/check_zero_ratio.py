"""Seven zeros pure varied off pair with zero reflected ratio and terminal duplicate."""
import sys
rear=sys.argv[1]
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


T,D=ring('D',K);R,X=ring('X',T.to_domain())
x=lambda u:R(T(u))
a=1+2*U
W=(2*V) if rear=='arith' else 2-V
s=D-1-W;t=D-1-V;r=D-1
p=(2*W*V+1+2*W-W*W)/(2*V)
def det(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
I=lambda P:sum((z*D**i*C(1,i+1) for (i,),z in P.items()),T.zero)
P3=(X-x(s))*(X-x(t))*(X-x(r))
Pa=[C(1)+U,-2-U,K.one]
def J(P,k,x0):
 return sum((x(z*C(1,j+k+1))*x0**(j+k+1) for j,z in enumerate(P)),R.zero)
def E(P,x0):return sum((x(z)*x0**j for j,z in enumerate(P)),R.zero)
def L(x0):return 70*x0**4-140*x(D)*x0**3+90*x(D*D)*x0*x0-20*x(D**3)*x0+x(D**4)
def G(x0):return L(x(a))*(x(a)*(J(Pa,0,x0)-E(Pa,x0))+x0*E(Pa,x0)-J(Pa,1,x0))-L(x0)*(x(a)*E(Pa,x(a))-J(Pa,1,x(a)))
gg=G(X)
# a equals the repeated ordinary terminal label, so D is fixed.
D0=1+a;Q0,Y=ring('Y',K)
def d_eval(h):return h.evaluate(D,D0)
def x_eval(h):return Q0.from_dict({k:d_eval(c) for k,c in h.items()})
P=x_eval(P3)
def It(P):return sum((z*D0**i*C(1,i+1) for (i,),z in P.items()),K.zero)
mm=[It(P*Y**k) for k in range(5)]
R3=p*(P//(Y-d_eval(s)))-V*(P//(Y-d_eval(t)))
mr=[It(R3*Y**k) for k in range(4)]
M=[[mm[0],mm[1],mm[2]],[mm[1],mm[2],mm[3]],[mr[0],mr[1],mr[2]]]
rhs=[-mm[3],-mm[4],-mr[3]]
dd=det(M);print('fixed ordinary pivot',bool(dd),flush=True)
ns=[]
for i in range(3):
 M1=[r[:] for r in M]
 for j in range(3):M1[j][i]=rhs[j]
 ns.append(det(M1))
if not dd:
 assert any(ns)
else:
 n0,n1,n2=[n/dd for n in ns]
 q=Y**3+n2*Y*Y+n1*Y+n0
 print('fixed second gate gcd',q.gcd(x_eval(gg)).degree(),flush=True)
 assert q.gcd(x_eval(gg)).degree()==0

# Four distinct known labels, two further literal early clocks.
P4=P3*(X-x(a));m=[I(P4*X**k) for k in range(4)]
R4=x(p)*(P4//(X-x(s)))-x(V)*(P4//(X-x(t)))
r0,z0,w0=[I(R4*X**k) for k in range(3)]
rows=[[m[0],m[1],m[2]],[m[1],m[2],m[3]],[r0,z0,w0]]
H=det(rows)
def strip(H,guards):
 for z in guards:
  while True:
   g=H.gcd(z)
   if g.degree()==0:break
   H=H//g
 return H
H=strip(H,[D,s-a,t-a,r-a])
print('regular projection factors',[(g.degree(),n) for g,n in H.factor_list()[1]],flush=True)
assert [(g.degree(),n) for g,n in H.factor_list()[1]]==[(9,1)]
from itertools import combinations
for f,n in H.factor_list()[1]:
 f=f.monic()
 def rd(q):return T(q)%f
 def inv(q):
    a,b,g=(q%f).gcdex(f)
    assert g==T.one
    return a%f
 E0=None
 for i,j in combinations(range(3),2):
    a0,a1,a2=rows[i]; b0,b1,b2=rows[j]
    de=rd(a0*b1-a1*b0)
    if not de:continue
    E0=(rd((a1*b2-a2*b1)*inv(de)),rd((a2*b0-a0*b2)*inv(de)))
    break
 assert E0 is not None
 q0,q1=E0
 assert all(not rd(x0*q0+x1*q1+x2) for x0,x1,x2 in rows)
 q=X*X+x(q1)*X+x(q0)
 gm=gg%q
 g0=rd(gm.get((0,),T.zero));g1=rd(gm.get((1,),T.zero))
 z=rd(g0*g0-q1*g0*g1+q0*g1*g1)
 b=rd(gg.evaluate(X,r))
 print('field degree',f.degree(),'terminal gate',bool(b),'quadratic norm',bool(z),flush=True)
 assert b and z
