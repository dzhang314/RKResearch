"""Exact 4x4 separated endpoint determinant, minor and raw pressure replay."""
import sympy as S
b,z,c,d,Y,W,U,A,B=S.symbols("b z c d Y W U A B")
q=S.Rational
same=lambda f,g:S.cancel(f-g)==0
D=2*b-3
Lb=2/(b*D);L1=-2
Q=(z-1)*(q(1,2)-z/D)
P=1-z/3
R=1-z/2-(b-1)*z*(z-1)/(2*D)
actual_tap=-q(1,2)*(1+Lb*b*b/2)
assert same(Q.subs(z,b),actual_tap)
assert same(-2*actual_tap,Lb*b*b/2+1)
assert same(-2*actual_tap,Lb*b**3/3+P.subs(z,b))
assert same(-2*actual_tap,Lb*b**4/4+R.subs(z,b))
M=S.Matrix([[1,b,0,Q],[L1,b*Lb,-z*z/2,1],
 [L1,b*b*Lb,-z**3/3,P],[L1,b**3*Lb,-z**4/4,R]])
Dt=z**3*(z-b)**2*(b-1)*(z-1)/D**2
assert same(M.det(method="domain-ge"),Dt)
print("first separated jump: augmented determinant",S.factor(Dt))
at1=M.extract([0,2,3],range(3)).det(method="domain-ge").subs(z,1)
atb=M.extract([0,1,2],range(3)).det(method="domain-ge").subs(z,b)
assert same(at1,b*(b-1)/D)
assert same(atb,-4*b**3*(b-2)*(b-1)/(3*D))
print("repeated-row minors: first 1 can't recur; repeat b only at b=2")
cleared=S.Matrix([[2*D,2*b*D**2,0,(z-1)*(D-2*z)],
 [-4,4,-z*z,2],[-6,6*b,-z**3,3-z],
 [-8*D,8*b*b*D,-z**4*D,4*D-2*D*z-2*(b-1)*z*(z-1)]])
assert all(same(x,0) for x in cleared-S.diag(2*D,2,3,4*D)*M*S.diag(1,D,1,1))
assert S.expand(cleared.det(method="domain-ge")-48*D*z**3*(z-b)**2*(b-1)*(z-1))==0
print("denominator-cleared determinant for portable Lean confirmed")
p2=W*z*z/2+U
p3=W*z**3/3+P*U
p4=W*z**4/4+R.subs(b,2)*U
assert S.expand(p4-3*p3+2*p2-z*(z-2)*(W*z*(z-2)-2*U)/4)==0
mp=Y*Y*(Y-2)**2
gp=(Y-c)*S.diff(mp,Y)/4
J=lambda f:S.integrate(f,(Y,0,z))
assert S.expand(4*J(gp)-(z-c)*mp.subs(Y,z)+J(mp))==0
assert same(1/(1-c)+1/(c-1),0)
assert same(1/((1-c)*(1-d))+1/((c-1)*(c-d))+1/((d-1)*(d-c)),0)
print("two-label primitive ratio and raw cardinal/terminal collapse confirmed")
