"""Six zeros, silent varying triple, nonzero kappa and auxiliary ghost."""
import sympy as S
from itertools import product
from time import monotonic
from sympy.polys.rings import ring
u,v,z=S.symbols('u v z')
Q=u**3-3*u**2+S.Rational(3,4)*u+S.Rational(1,2)
H=v**3-4*v**2-v+2
f=S.Poly(S.resultant(Q,H.subs(v,(z-u)/2),u),z).monic()
assert f.degree()==9 and f.is_irreducible
red=lambda p:S.rem(S.rem(S.expand(p),Q,u),H,v)
basis=[u**i*v**j for i in range(3) for j in range(3)]
vec=lambda a:S.Matrix([S.Poly(a,u,v).coeff_monomial(e) for e in basis])
C=S.Matrix.hstack(*(vec(red((u+2*v)**k)) for k in range(9)))
E=C.inv()
coU=E*vec(u);coV=E*vec(v)
assert red(sum(c*(u+2*v)**i for i,c in enumerate(coU))-u)==0
assert red(sum(c*(u+2*v)**i for i,c in enumerate(coV))-v)==0
assert red(f.as_expr().subs(z,u+2*v))==0
K=S.QQ.algebraic_field((f,z));S0,D=ring('D',K)
t=K.unit
U=sum((K.convert(c)*t**i for i,c in enumerate(coU)),K.zero)
V=sum((K.convert(c)*t**i for i,c in enumerate(coV)),K.zero)
assert U+2*V==t
C=lambda a,b=1:K.convert(S.Rational(a,b))
def det(M):
 x,y,z=M
 return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
a=1+2*U
P0=[1+U,-2-U,K.one]

for i in (0,1):
 D=2+i*U+2*V
 d=1+i*U
 t=D-1-V;s=D-1
 assert D and len({a,t,s,d})==4
 R,X=ring(f'X{i}',K)
 def I(p):return sum((c*D**j*C(1,j+1) for (j,),c in p.items()),K.zero)
 def L(x):return 70*x**4-140*D*x**3+90*D*D*x*x-20*D**3*x+D**4
 def ev(x):return sum((p*x**i for i,p in enumerate(P0)),R.zero)
 def J(k,x):return sum((p*x**(i+k+1)*C(1,i+k+1) for i,p in enumerate(P0)),R.zero)
 assert L(a) and J(0,R(a))==ev(R(a))
 P3=(X-a)*(X-s)*(X-t)
 m=[I(P3*X**i) for i in range(5)]
 kappa=1+2*V-V*V
 assert kappa
 B=kappa*(P3//(X-t))-2*(P3//(X-s))
 b=[I(B*X**i) for i in range(4)]
 M=[[m[0],m[1],m[2]],[m[1],m[2],m[3]],[b[0],b[1],b[2]]]
 E=det(M)
 print(i,'three coefficient pivot',bool(E))
 assert E
 rhs=[-m[3],-m[4],-b[3]]
 n=[]
 for j in range(3):
  X0=[x[:] for x in M]
  for k in range(3):X0[k][j]=rhs[k]
  n.append(det(X0)/E)
 assert all(sum((M[i][j]*n[j] for j in range(3)),K.zero)==rhs[i] for i in range(3))
 P=X**3+n[2]*X**2+n[1]*X+n[0]
 H=L(a)*(a*(J(0,X)-ev(X))+X*ev(X)-J(1,X))-L(X)*(a*ev(R(a))-J(1,R(a)))
 assert P.gcd(H).degree()==0
 print(i,'guarded forward gcd 0')
