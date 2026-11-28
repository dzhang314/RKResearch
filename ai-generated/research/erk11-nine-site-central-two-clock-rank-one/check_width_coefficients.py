"""Exact scalar audit for the half-half ERK11 central bilinear gate."""
import sympy as S

x, a, d, t = S.symbols('x a d t')

def integral(expr):
    return S.integrate(S.Poly(expr, x).as_expr(), (x, 0, 1))

V_a = x**2 * (x-a)**2
V_b = (1-x)**2 * (x-d)**2
P = S.integrate(V_a, x)
Q = S.integrate(V_b, (x, x, 1))
H = integral(P*V_b)
J = integral(P*Q)
C1, C2 = integral(x*P*V_b), integral(x*V_a*Q)
I0, I1, I2 = (integral(x**i*V_a*V_b) for i in range(3))
assert S.expand(H-integral(V_a*Q)) == 0
assert S.expand(J-C1+C2) == 0
A = H**2-J*I0
B, C = J*I1-H*C1, J*I1-H*C2
D = C1*C2-J*I2
Delta = S.factor(A*D-B*C)
assert S.expand(4*I0*Delta-J*((I0*J)**2-
    (2*H*I1-I0*(C1+C2))**2-4*A*(I0*I2-I1**2))) == 0
print('Exact primitive and centered determinant identities')

def half(expr):
    return S.expand(expr.subs({d:a-1}).subs({a:t+1}))

F4 = 33*t**4-22*t**2+5
F6 = 2475*t**6-2985*t**4+921*t**2-59
assert S.expand(41580*half(J)-F4) == 0
assert S.expand(3*F4-11*(3*t**2-1)**2-4) == 0
assert S.expand(1646877554784000000*half(Delta)+(t*t-1)**2*F4*F6) == 0
assert S.gcd(S.Poly(half(A),t),S.Poly(half(Delta),t)).degree() == 0
assert S.gcd(S.gcd(S.Poly(half(B),t),S.Poly(half(C),t)),S.Poly(half(D),t)).degree() == 0
print('Half-half determinant exact factorization and both coefficient gcds certified')
