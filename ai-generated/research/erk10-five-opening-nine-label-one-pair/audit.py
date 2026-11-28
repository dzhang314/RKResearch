"""Exact determinant and weighted terminal replay for the nine-label chart."""
import sympy as S
b,c,z,k,H,f,g,h,d,a,e,Y = S.symbols("b c z k H f g h d a e Y")
q=S.Rational
same=lambda x,y:S.cancel(x-y)==0
a1=S.Integer(1)
L1=S.Integer(-2)
Lb=-2*(1+2*k*(b-1))/b**2
delta=3*b*k-2*c*k+c
lam=b*k/((b-1)*delta)
Q=k*(z-1)+(b-1)*lam*(z-1)*(z-b)
P=2*z/3+k*(4*b/3-2)*(z-1)
R0=z*z/2+k*(b*b-2)*(z-1)
x1=(c-1)*(k-lam*(c-b))
xb=lam*(c-1)*(c-b)
Lc=S.factor(2/c**2*(x1*L1+xb*Lb*b-1))
D=S.factor((x1*L1+xb*Lb*b**3-Lc*c**4/4-R0.subs(z,c))/((c-1)*(c-b)))
R=R0+D*(z-1)*(z-b)
assert same(x1+xb,k*(c-1)) and same(x1+b*xb,Q.subs(z,c))
assert same(x1*L1+xb*Lb*b**2,Lc*c**3/3+P.subs(z,c))
assert same(D,-b*k*(b*k-c*k-c+2)/delta)
assert same(Lc,-2*(2*b*c*k*k+2*b*c*k-2*b*k*k+b*k-2*c*k+c)/(c*c*delta))
print("the third row explicitly pays the actual two defect and three primitive reads")

M=S.Matrix([[1,1,1,0,k*(z-1)],
 [1,b,c,0,Q],
 [L1,b*Lb,c*Lc,-z*z/2,1],
 [L1,b*b*Lb,c*c*Lc,-z**3/3,P],
 [L1,b**3*Lb,c**3*Lc,-z**4/4,R]])
det=S.factor(M.det(method="domain-ge"))
expect=-2*b*k**3*z**2*(z-b)*(b-1)*(b-c)*(z-c)**2*(c-1)*(2*k-1)*(z-1)/(c*delta**2)
assert same(det,expect)
print("fourth distinct physical row determinant:",det)
minor1=S.factor(M.extract([0,1,3,4],range(4)).det(method="domain-ge"))
minor2=S.factor(M.extract(range(4),range(4)).det(method="domain-ge"))
common=(b-1)*(b-c)*(c-1)
assert same(minor1,-k*z**3*common*(-4*b*k+2*k*z-z)/delta)
assert same(minor2,2*z*z*common*(2*k-1)*(3*b*c*k+b*k*z-2*c*k*z+c*z)/(3*b*c*delta))
numer1=(3*b*c*k+b*k-2*c*k+c)
assert same(numer1-b*k*(1-c),c*(4*b*k-2*k+1))
assert same((b*k+c*k+c).subs(k,-q(1,2)),(c-b)/2)
assert same((-4*b*k+2*c*k-c).subs(c,4*b*k/(2*k-1)),0)
print("repeat minors: 1 and b have full rank; c needs c(2κ−1)=4bκ")

CC=4*b*k/(2*k-1)
A=S.Matrix([[1,1,1,0,0],[1,b,CC,0,0],
            [L1,b*Lb,0,CC,-z*z/2],[L1,b*b*Lb,0,CC**2,-z**3/3],
            [L1,b**3*Lb,0,CC**3,-z**4/4]])
rhs=S.Matrix([k*(z-1),Q.subs(c,CC),1,P,R.subs(c,CC)])
act=S.factor(A.det(method="domain-ge"))
assert same(act,-2*b*k*z*z*(b-1)*(2*k+1)*(-4*b*k+(2*k-1)*z)**2*
            (4*b*k-2*k+1)/(2*k-1)**4)
A[:,4]=rhs
N=lambda z:2*(4*b*k*k*z-4*b*k*k+2*b*k*z+2*b*k-2*k*z+z)/(2*k-1)
assert same(A.det(method="domain-ge")/act,N(z)/(z*z*(z-CC)))
assert same(L1,N(1)/(1-CC))
assert same(Lb,N(b)/(b*b*(b-CC)))
assert same(L1*(1-CC/2),CC-2)
assert same(Lb*b*(b-CC/2),CC-2)
print("after the close, independent scalar ratio N(Y)/[Y²(Y−c)]; two anchor cancellations")

Mp=Y*Y*(Y-c)**2
Gp=(Y-d)*S.diff(Mp,Y)/4
J=lambda F:S.integrate(F,(Y,0,z))
assert S.expand(4*J(Gp)-(z-d)*Mp.subs(Y,z)+J(Mp))==0
for sites in ([a,b,d],[a,b,d,e]):
 for power in (0,1):
  assert same(sum(x**power/S.prod(x-y for y in sites if y!=x) for x in sites),0)
print("blind primitive derivative and raw affine 3/4-site cofactors verified")

# Degenerate κ=1/2: literal next row imposes w Y + 2u=0.
w,u=S.symbols("w u")
assert S.expand(w*z*z/2+u+(z-1)*u-z*(w*z+2*u)/2)==0
print("κ=1/2 propagates the forbidden raw u=−wY/2 relation")
