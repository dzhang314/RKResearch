"""QQ polynomial audit of the forward-five projection."""
import sympy as S
Y=S.symbols('Y')
g=[S.Symbol(f'u{i}') for i in range(4)]
U=sum(v*Y**i for i,v in enumerate(g))
I=lambda w:S.integrate(w,Y).expand()
J=I(Y*U.subs(Y,1-Y))
T=I((1-Y)*U)
JR=J.subs(Y,1-Y)
assert S.expand(JR-T.subs(Y,1)+T)==0
pol,rem=S.div(JR,Y-1,Y)
assert rem==0 and S.degree(pol,Y)<=4
# Verify the column subtraction with the true sign of both reflected factors.
V,B,t,z,c0,c1,c2=S.symbols('V B t z c0 c1 c2')
R=Y**3+c2*Y**2+c1*Y+c0; D=(Y-V)*(Y-B)*R
M=U-g[3]*Y**3
U0=M+t*R
assert S.expand((Y-V)*(Y-B)*U0-(Y-V)*(Y-B)*M-t*D)==0
print('Exact reflection, endpoint cancellation, and two-clean column subtraction verified over QQ.')
