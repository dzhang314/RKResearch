"""Exact shifted Jacobi orthogonality over the rational coefficient field."""
import sympy as S
Y=S.symbols('Y')
J4=42*Y**4-84*Y**3+56*Y**2-14*Y+1
J5=132*Y**5-330*Y**4+300*Y**3-120*Y**2+20*Y-1
Eminus=66*Y**4-120*Y**3+72*Y**2-16*Y+1
assert S.expand(2*(Y-1)*Eminus-J5+J4)==0
M=S.Matrix([[S.Rational(2,(i+j+2)*(i+j+3)*(i+j+4))for j in range(4)]for i in range(4)])
assert M.det()==S.Rational(1,2240421120000)
assert all(S.integrate(Y*(1-Y)**2*Eminus*Y**i,(Y,0,1))==0 for i in range(4))
print('Exact degree-four weighted Jacobi line and its independent minor verified.')
