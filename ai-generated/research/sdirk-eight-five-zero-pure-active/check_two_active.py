"""Exact pure supported two-active frame."""
import sympy as S
from sympy.polys.rings import ring
V=S.symbols("v")
Q=lambda v:4*v**3-12*v*v+3*v+2
f=S.Poly(Q(V),V)
assert f.is_irreducible
assert S.gcd(f,S.Poly(Q(-V),V)).degree()==0
K=S.QQ.algebraic_field((f,V));v=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
D=2+v;a=1+2*v;s=1-v
assert D and a!=s
R,B=ring('b',K)
def L(t):return 70*t**4-140*D*t**3+90*D**2*t*t-20*D**3*t+D**4
assert L(R(s)) and L(R(a))
P=[1+v,-2-v,K.one]
def ev(t):return P[0]+P[1]*t+t*t
def J(j,t):return sum((p*t**(i+j+1)*C(1,i+j+1) for i,p in enumerate(P)),R.zero)
assert not (J(0,R(a))-ev(R(a)))
m=[D**(k+2)*C(1,k+3)-(a+s)*D**(k+1)*C(1,k+2)+a*s*D**k*C(1,k+1) for k in range(6)]
def det(M):
 x,y,z=M
 return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
M=[[m[i+j] for j in range(3)] for i in range(3)]
Delta=det(M);assert Delta
N=[]
for i in range(3):
 m0=[x[:] for x in M]
 for j in range(3):m0[j][i]=-m[j+3]
 N.append(det(m0)/Delta)
assert all(not (sum((m[i+j]*N[j] for j in range(3)),K.zero)+m[i+3]) for i in range(3))
q=B**3+N[2]*B*B+N[1]*B+N[0]
g=L(R(a))*(a*(J(0,B)-ev(B))+B*ev(B)-J(1,B))-L(B)*(a*ev(R(a))-J(1,R(a)))
gg=q.gcd(g)
print("pure two-active: ordinary fifth sites and forward second gate gcd degree",gg.degree())
assert gg.degree()==0
