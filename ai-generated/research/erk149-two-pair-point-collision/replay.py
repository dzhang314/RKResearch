#!/usr/bin/env python3
"""Exact symbolic scalar calculations for the stipulated A,B,A',B' prefix."""
from sympy import Matrix, Rational, cancel, factor, symbols, sympify

a, b, x, y = symbols("a b x y")
s = symbols("s")
G = (a+b)*s**3/3 - a*b*s**2/2 - s**4/4
assert factor(G.subs(s, a)) == a**3*(a-2*b)/12
assert factor(G.subs(s, b)) == -b**3*(2*a-b)/12

def two_taps(t):
    return (Matrix([[a,b],[a**2,b**2]]).inv()
            * Matrix([t**2/2,t**3/3])).applyfunc(cancel)

wa, wb = two_taps(a)
assert cancel(wa - a*(3*b-2*a)/(6*(b-a))) == 0
assert cancel(wa.subs(a,2*b) - b/3) == 0
wa, wb = two_taps(b)
assert cancel(wa.subs(b,2*a) - 4*a/3) == 0
assert cancel(wb.subs(b,2*a) - a/3) == 0

# At r=A: the two paid h and u equations determine the honest tap products.
h = -a**2*x/2-a**4/3
u = -(4*a/3)*a**2/2+a*x+2*a*y
g = -(4*a/3)*a**3/3+a**2*x+(2*a)**2*y+(a/3)*(-2*a**3/3)
pt = {x:-2*a**2/3, y:2*a**2/3}
assert cancel(h.subs(pt)) == 0
assert cancel(u.subs(pt)) == 0
assert factor(Matrix([[h.diff(x),h.diff(y)],[u.diff(x),u.diff(y)]]).det()) == -a**3
assert cancel(g.subs(pt) - 4*a**4/3) == 0

# Check the pulled-word expansions in a formal indeterminate module.
# Monomials y^j represent clock-polynomial rows; symbols carry actual defects.
u, g, h, k, Yu, LYu, Lg, Lh = symbols("u g h k Yu LYu Lg Lh")
def L(v):
    v = sympify(v).expand()
    ys = ((y,v.coeff(y,1)), (y**2,v.coeff(y,2)), (y**3,v.coeff(y,3)))
    return (v.coeff(y,0).subs({u:0,g:0,h:0,Yu:0})*y
            + ys[0][1]*(y**2/2+u) + ys[1][1]*(y**3/3+g)
            + ys[2][1]*(y**4/4+k)
            + v.coeff(u)*h + v.coeff(g)*Lg + v.coeff(h)*Lh + v.coeff(Yu)*LYu).expand()
def C(v):
    v = sympify(v).expand()
    return ((1-y)*(v.subs(u,0)) + v.coeff(u)*(u-Yu)).expand()
T = L
assert (T(C(1 + 0*y))-(y-y**2/2)).expand() == -u
assert (T(C(C(y*0+1)))-(y-y**2+y**3/3)).expand() == g-2*u
assert (T(T(T(y*0+1)))-y**3/6).expand() == g/2+h
assert (T(C(C(C(y*0+1))))-(y-3*y**2/2+y**3-y**4/4)).expand() == -3*u+3*g-k
assert (T(C(T(C(y*0+1))))-(y**2/2-y**3/2+y**4/8)).expand() == u-Rational(3,2)*g+k/2-h+LYu
assert (T(T(C(T(y*0+1))))-(y**3/6-y**4/12)).expand() == g/2-k/3+h-Lg
assert (T(T(T(T(y*0+1))))-y**4/24).expand() == k/6+Lg/2+Lh
print("Both pair cubics, tap resonance, 4a^4/3, and all seven literal reverse words verified exactly.")
