"""Exact m=8 repeated endpoint arithmetic, no score division."""
import sympy as S
a,b,c,z,k,d=S.symbols("a b c z k d")
r=S.Rational
same=lambda f,g:S.cancel(f-g)==0
Fa=lambda a,b,z:-z*z/4+(a+b)*z/3-a*b/2
cases=[]
beta=-r(2,3);phi=-a-(b-a)*(z-a)/(2*b-3*a);psi=-a*(z-a)/(2*b-3*a)
q,D=(2*b-a)/4,-a/2
cases.append((phi-(a+b)*beta,psi-q*beta-D))
beta=(4*b-6*a)/(3*a);pb=b*b/a-2*a
pa=(a+b)*beta-b*(a-2*b)/(3*(3*b-2*a))
psa=b*(a-b)/(3*b-2*a)
phi=pb+(z-b)*(pa-pb)/(a-b);psi=(z-b)*psa/(a-b)
q,D=a*(2*a-b)/(4*b),-a*(3*b-2*a)/(2*b)
cases.append((phi-(a+b)*beta,psi-q*beta-D))
hc=a*c*c*(2*c-3*b)/(4*b)
pc=c*c*Fa(a,b,c)/hc+(a+b)*beta
phi=pb+(z-b)*(pc-pb)/(c-b);psi=-b*(z-b)/(2*c-3*b)
q,D=a*(2*c-b)/(4*b),-c+a*(2*c-b)/(2*b)
eta=-a/(2*(a-b)*(a-c))
cases.append((phi-(b+c)*beta-1/eta,psi-q*beta-D))
wants=[
 (b*(5*a-4*b)/(3*(3*a-2*b)),b*(a-2*b)/(3*(3*a-2*b))),
 (b*(4*a-5*b)/(3*(2*a-3*b)),a*(2*a-b)/(3*(2*a-3*b))),
 (b*c*(5*b-4*c)/(3*a*(3*b-2*c)),c*(b-2*c)/(3*(3*b-2*c)))]
for inp,w in zip(cases,wants):
 assert all(same(e.subs(z,0),f) for e,f in zip(inp,w))
print("three zero-endpoint head coefficient pairs cannot vanish in a paid field")

CC=4*b*k/(2*k-1)
L1=-2; Lb=-2*(1+2*k*(b-1))/b**2
Delta=3*b*k-2*CC*k+CC
Q=k*(z-1)+b*k*(z-1)*(z-b)/Delta
P=2*z/3+k*(4*b/3-2)*(z-1)
R=z*z/2+k*(b*b-2)*(z-1)-b*k*(b*k-CC*k-CC+2)*(z-1)*(z-b)/Delta
A=S.Matrix([[1,1,1,0,k*(z-1)],[1,b,CC,0,Q],
 [L1,b*Lb,0,CC,1],[L1,b*b*Lb,0,CC**2,P],[L1,b**3*Lb,0,CC**3,R]])
D0=-32*b**3*k**3*(b-1)*(2*k+1)*(4*b*k-2*k+1)/(2*k-1)**3
assert same(A.subs(z,0).det(method="domain-ge"),D0)
print("zero target after repeated c:",S.factor(D0))

N=lambda y:2*(4*b*k*k*y-4*b*k*k+2*b*k*y+2*b*k-2*k*y+y)/(2*k-1)
assert same(N(0),-4*b*k)
for ys in ([1,b,d],[1,b,d,z]):
 for j in [0,1]:
  assert same(sum(y**j/S.prod(y-t for t in ys if t!=y) for y in ys),0)
assert same(sum(1/(y*S.prod(y-t for t in [1,b,d] if t!=y)) for y in [1,b,d]),1/(b*d))
print("affine cofactor, and missing-Y pole gives N(0)/(b*d)")
