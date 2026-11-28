"""Exact scalar checks for lifting/folding a zero-total triple's weights."""
import sympy as S
a,b,z,L,T,W1,W2,V1,V2,rho,B1,B2 = S.symbols("a b z L T W1 W2 V1 V2 rho B1 B2")
weights = S.Matrix([W1,W2,-W1-W2])
mode = S.Matrix([V1,V2,-V1-V2])
assert (mode-weights).subs({V1:W1,V2:W2})==S.zeros(3,1)
print("tracking two copies extends by both zero sums, even at zero score")
v1=S.Matrix([-rho*B1,B1])
v2=S.Matrix([-rho*B2,B2])
assert S.expand(S.det(S.Matrix.hstack(v1,v2)))==0
print("lifting w_a imposes A+rho B=0, so two old scalar tap rows have rank ≤1")
e2=a*a*L+2*a*T-z*z
e3=a**3*L+3*a*a*T-z**3
e4=a**4*L+4*a**3*T-z**4
assert S.expand(a*a*e2-2*a*e3+e4+z*z*(z-a)**2)==0
print("calibrated second-target square:",S.factor(a*a*e2-2*a*e3+e4))
