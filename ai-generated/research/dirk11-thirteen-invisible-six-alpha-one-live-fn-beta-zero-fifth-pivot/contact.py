import sympy as S
Y,z,c0=S.symbols('Y z c0')
J4=42*Y**4-84*Y**3+56*Y**2-14*Y+1
J5=132*Y**5-330*Y**4+300*Y**3-120*Y**2+20*Y-1
mu=S.Rational(11,7)*(1-2*z)
T=(J5+mu*J4)/132
R=Y**3-4*z*Y**2+6*z*z*Y+c0
U=Y**2-(2-3*z)*Y+S.Rational(14,11)-6*z+6*z*z
D=S.Poly(S.expand(R*U-T),Y)
print('old contact R', R)
print('deflated difference',D)
cc=S.solve(D.nth(2),c0)[0]
print('constant recovery',S.factor(cc))
f=S.Poly(D.nth(1).subs(c0,cc),z).clear_denoms()[1].primitive()[1]
g=S.Poly(D.nth(0).subs(c0,cc),z).clear_denoms()[1].primitive()[1]
print('primitive one and zero',f,g)
u,v,gcd=S.gcdex(f,g)
print('ordinary gcd',gcd)
print('integer bezout multiplier/coeffs',S.ilcm(*[c.q for c in (*u.all_coeffs(),*v.all_coeffs())]),u,v)
assert gcd==1 and u*f+v*g==gcd
