"""Verify the rational factor used to select the symmetric reverse mesh."""
import sympy as S
x, a, b, c = S.symbols("X a b c")
early = [a, -a, b]
remaining = [S.S(0), -b, c, -c]
F = S.Poly((x + 1) * S.prod(x - r for r in remaining), x)
def I(f):
    return S.Add(*(2 * v / (d + 1) for (d,), v in S.Poly(f, x).terms() if d % 2 == 0))
def R(f):
    p = S.Poly(f, x).integrate()
    return p.eval(1) - p.as_expr()
pieces = []
for z in early:
    ell = (x - 1) * S.prod(x - u for u in early if u != z)
    # The common interpolation denominator cancels in the quotient.
    h = S.prod(z - u for u in early if u != z)
    pieces.append(S.factor(I(F.as_expr() * R(ell))) / (h * S.factor(I(F.as_expr() * ell))))
want = -2*(7*c**2 - 3)*(6*b*c**2 - 3*b - 3*c**2 + 2)/(
    (21*a**2*c**2 - 9*a**2 - 9*c**2 + 5) *
    (21*b**2*c**2 - 9*b**2 - 9*c**2 + 5))
assert S.cancel(sum(pieces) - want) == 0
assert want.subs({a:S.Rational(1,3), b:S.Rational(5,6), c:S.Rational(1,2)}) == 0
print("exact centered-mesh compatibility factor and selected specialization verified")
