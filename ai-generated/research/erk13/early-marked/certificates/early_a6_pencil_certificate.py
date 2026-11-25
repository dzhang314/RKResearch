#!/usr/bin/env python3
"""Exact algebraic certificate for two early marked ERK13 pencil gates.

Requires SymPy. Only integer, rational, and finite-field polynomial operations.
The companion proof explains the domain restrictions and characteristic-zero lift.
"""
import sympy as s

x, t, z = s.symbols("x t z")


def F(v):
    return 132*v**5-330*v**4+300*v**3-120*v**2+20*v-1


def j(v):
    return 1716*v**6-5544*v**5+6930*v**4-4200*v**3+1260*v**2-168*v+7


def J(v):
    return v*j(v)


def prim(poly, k, at):
    return sum(coef*at**(power[0]+k+1)/(power[0]+k+1)
               for power, coef in s.Poly(poly, x).terms())


def primitive_integer(expr, *symbols):
    return s.Poly(expr, *symbols).clear_denoms()[1].primitive()[1].as_expr()


def exact_div(poly, factor, *symbols):
    return s.Poly(poly, *symbols).exquo(s.Poly(factor, *symbols)).as_expr()


def assert_identity(left, right):
    assert s.expand(left-right) == 0


def residue_chart(A, C, z_power, degree, p):
    # Both last subresultants are in the ideal (A,C). Remove only the
    # explicit nonzero z power and integer contents.
    seq = s.subresultants(A, C, t)
    assert [s.degree(si, t) for si in seq[-2:]] == [1, 0]
    R0 = primitive_integer(exact_div(seq[-1], z**z_power, z), z)
    S1 = primitive_integer(exact_div(seq[-2], z**z_power, t, z), t, z)
    assert s.degree(R0, z) == degree and R0.subs(z, 0) != 0
    S = s.Poly(S1, t).nth(1)
    T = s.Poly(S1, t).nth(0)

    def pol(expr):
        return s.Poly(expr, z, modulus=p)

    R = pol(R0).monic()
    assert R.degree() == degree

    def rem(expr):
        return pol(expr).rem(R)

    def mul(a, b):
        return (a*b).rem(R)

    def inv(a):
        return a.invert(R).rem(R)

    t0 = mul(-rem(T), inv(rem(S)))

    def ev(expr):
        result = pol(0)
        for coef in s.Poly(expr, t).all_coeffs():
            result = (mul(result, t0)+rem(coef)).rem(R)
        return result

    assert ev(A).is_zero and ev(C).is_zero
    return rem, mul, inv, ev


def trim(terms):
    while terms and terms[-1].is_zero:
        terms.pop()
    return terms


def check_cubic():
    A0 = x**2-6*x/5+s.Rational(3, 10)
    B0 = x**3-6*x/5+s.Rational(2, 5)
    P = 15*(4*z-3)*B0-10*(5*z*z+4*z-6)*A0
    D = (5*z-2)*(7*z-6)
    N = 100*z**4-460*z**3+819*z**2-672*z+210

    # Verify the physical equations normalize to the displayed pencil gate.
    for basis in [A0, B0]:
        for k in [1, 2]:
            assert_identity(prim(basis, k, 1), 0)
    assert_identity(prim(A0, 2, z)-prim(A0, 1, z),
                    z*z*(z-1)**2*(4*z-3)/20)
    assert_identity(prim(B0, 2, z)-prim(B0, 1, z),
                    z*z*(z-1)**2*(5*z*z+4*z-6)/30)
    assert_identity(prim(P, 3, 1), -D/420)
    assert_identity(prim(P, 3, z)-prim(P, 2, z), z**4*N/420)

    Ap = exact_div(D*F(t*z)+z**3*N*F(t), z-1, t, z)
    Bp = exact_div(D*j(t*z)+z**3*N*j(t), z-1, t, z)
    C = exact_div(Bp+7*Ap, t, t, z)
    rem, mul, inv, ev = residue_chart(Ap, C, 15, 50, 43)
    H = F(t)*j(t*x)-j(t)*F(t*x)
    hp = [ev(s.Poly(H, x).nth(k)) for k in range(7)]
    pp = [rem(s.Poly(P, x).nth(k)) for k in range(4)]

    def remainder(lhs, rhs):
        leading_inverse = inv(rhs[-1])
        lhs = lhs.copy()
        while lhs and len(lhs) >= len(rhs):
            q = mul(lhs[-1], leading_inverse)
            k = len(lhs)-len(rhs)
            for i, b0 in enumerate(rhs):
                lhs[k+i] -= mul(q, b0)
            trim(lhs)
        return lhs

    degrees = []
    while pp:
        degrees.append(len(pp)-1)
        hp, pp = pp, remainder(hp, pp)
    assert degrees == [3, 2, 1, 0]
    print("cubic pencil: degree-50 chart mod 43; Euclidean units 3, 2, 1, 0")


def check_quartic():
    H = s.Poly(F(t)*j(t*x)-j(t)*F(t*x), x)
    quo, _ = s.div(H, s.Poly((x-1)*(x-z), x))
    W = exact_div(quo.as_expr(), t**2, x, t, z)
    assert s.degree(W, x) == 4
    A = primitive_integer(prim(W, 1, 1), t, z)
    M = primitive_integer(exact_div(H.eval(z), (z-1)*t, t, z), t, z)
    # The primitive difference is divisible by z before taking primitive
    # integer parts; no denominators in variables remain.
    mixed = s.Poly(prim(W, 2, z)-prim(W, 1, z), t, z)
    divided = mixed.exquo(s.Poly(z, t, z)).as_expr()
    B = primitive_integer(F(t*z)*prim(W, 2, 1)-F(t)*divided, t, z)
    _, _, inv, ev = residue_chart(A, M, 0, 40, 101)
    inv(ev(B))
    print("quartic pencil: degree-40 chart mod 101; third equation is a unit")


if __name__ == "__main__":
    check_cubic()
    check_quartic()
