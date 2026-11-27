"""Exact exclusion of the supported quadratic-line strict SDIRK8 chart.

Python 3 and python-flint 0.9.0 (no floating point or prime reduction).
Replay: python check_exclusion.py
"""
from functools import lru_cache
from itertools import permutations
from flint import fmpq, fmpq_mpoly_ctx, fmpq_poly

C = fmpq_mpoly_ctx.get(("k", "q", "g", "y"))
k, q, g, y = C.gens()
K = C.constant
x = k*k
r = y*y+k*y+q


def mirror(p):
    return p.compose(-k, q, g, y)


def parity(p):
    return (p+mirror(p))/2, (p-mirror(p))/(2*k)


def mean(p):  # uniform measure on [-1,1], with total mass one
    return sum(K(c/fmpq(d+1))*k**a*q**b*g**j
               for (a,b,j,d),c in p.terms() if d % 2 == 0)


def det3(M):
    return sum((-1)**sum(p[i] > p[j] for i in range(3) for j in range(i+1,3))
               *M[0][p[0]]*M[1][p[1]]*M[2][p[2]] for p in permutations(range(3)))


m = [mean(r*y**i) for i in range(6)]
Hankel = [[m[i+j] for j in range(3)] for i in range(3)]
T = -105*x*q-15*x+175*q**3+255*q*q+105*q+9
assert det3(Hankel) == 4*T/23625
p0,p1,p2 = [det3([[(-m[i+3] if j == ell else Hankel[i][j]) for j in range(3)]
                  for i in range(3)])*fmpq(23625,4) for ell in range(3)]
P = T*y**3+p2*y*y+p1*y+p0  # T times the monic zero-clock polynomial
assert all(not mean(r*P*y**j) for j in range(3))
A = -63*x*x*q+21*x*x-70*x*q**3-210*x*q*q-138*x*q-30*x+245*q**5+805*q**4+986*q**3+546*q*q+129*q+9
B = -525*x*x*q+525*x*x-1750*x*q**3-5670*x*q*q-3150*x*q-630*x+3675*q**5+13825*q**4+17970*q**3+9990*q*q+2259*q+153
omega = T*m[2]+p2*m[1]+p1*m[0]+(T*m[1]+p2*m[0])*y+T*m[0]*y*y
assert mean(r*r*P.derivative("y")) == 2*A/7
assert mean(r*omega) == B/315
diag = 180*g*A-B

R = r.compose(k,q,g,2*g-1)
D = R+4*g*g
U = 2*R-2*g*(4*g-2+k)
F = (-2*D**3+U*D**2+4*U**2*D-U**3-2*R*(3*U-2*D)*D)/(2*g)
G = 4*U**3-12*U**2*D+3*U*D**2+2*D**3
z = 2*g*(D+2*U)-D
pin = T*z**3+p2*z*z*D+p1*z*D*D+p0*D**3
primitive = 2*y**3+(3*k-12*g)*y*y+(6*q-12*g*k)*y+2-3*k+6*q-12*g*q
anchor = P.resultant(primitive,"y")


def strip(p, forbidden):
    """Divide out factors guaranteed nonzero at every admissible point."""
    while p:
        d = p.gcd(forbidden)
        if d.is_constant(): break
        p = p/d
    return p


def substitute_diagonal(p, num, den):
    """Clear the denominator of g=num/den without modulo or approximation."""
    n = p.degrees()[2]
    assert p.degrees()[3] == 0
    coeff = [dict() for j in range(n+1)]
    for (a,b,j,_),v in p.terms():
        coeff[j][a,b,0,0] = v
    return sum(C.from_dict(cs)*num**j*den**(n-j) for j,cs in enumerate(coeff) if cs)


def coeffs(p, var):
    """Coefficients in var, returned as ordinary rational polynomials in q."""
    names = p.context().names()
    i, qi = names.index(var), names.index("q")
    out = [dict() for j in range(p.degrees()[i]+1)]
    for e,c in p.terms():
        assert all(not power for j,power in enumerate(e) if j not in (i,qi))
        out[e[i]][e[qi]] = c
    return [fmpq_poly([cs.get(j,0) for j in range(max(cs,default=-1)+1)]) for cs in out]


def univar_q(p):
    var = next(v for v in p.context().names() if v != "q")
    assert p.degrees()[p.context().names().index(var)] == 0
    return coeffs(p,var)[0]


class Fiber:
    """Polynomials in the remaining variable over Q[q]/(M).

    Every inverse actually used in Euclid is checked, so there is no need to
    assume that M is presented irreducibly: each identity specializes at
    every root of M in any characteristic-zero field.
    """
    def __init__(self, modulus):
        self.M = modulus
        self.zero = fmpq_poly()
        self.one = fmpq_poly([1])

    @lru_cache(maxsize=500)
    def _inverse(self, cs):
        p = fmpq_poly(list(cs))
        d,a,_ = p.xgcd(self.M)
        assert d == 1 and (p*a) % self.M == 1
        return a % self.M

    def inv(self, p):
        return self._inverse(tuple(p.coeffs()))

    def clean(self, a):
        a = [c % self.M for c in a]
        while a and not a[-1]: a.pop()
        return a

    def divide(self, a, b):
        a,b = self.clean(a),self.clean(b)
        assert b
        result = [self.zero for _ in range(max(0,len(a)-len(b)+1))]
        inv = self.inv(b[-1])
        while len(a) >= len(b):
            j = len(a)-len(b)
            c = a[-1]*inv % self.M
            result[j] = c
            for i,d in enumerate(b[:-1]):
                a[j+i] = (a[j+i]-c*d) % self.M
            a.pop()
            while a and not a[-1]: a.pop()
        return result,a

    def gcd(self, a, b):
        a,b = self.clean(a),self.clean(b)
        while b:
            a,b = b,self.divide(a,b)[1]
        if not a: return []
        inv = self.inv(a[-1])
        return [c*inv % self.M for c in a]

    def gcds(self, polys):
        result = []
        for p in polys:
            result = self.gcd(result,p)
            if result == [self.one]: break
        return result

    def strip(self, a, forbidden):
        while len(a) > 1:
            d = self.gcd(a,forbidden)
            if len(d) <= 1: break
            a,rem = self.divide(a,d)
            assert not rem
        return a

    def add(self,a,b):
        out = list(a if len(a) >= len(b) else b)
        for i,c in enumerate(a if len(a) < len(b) else b): out[i] += c
        return self.clean(out)

    def mul(self,a,b):
        if not a or not b: return []
        out = [self.zero for _ in range(len(a)+len(b)-1)]
        for i,c in enumerate(a):
            for j,d in enumerate(b): out[i+j] += c*d
        return self.clean(out)


def projection_factors(v):
    return (35*v*v-3, 35*v*v+30*v+3,
            1225*v**8+9450*v**7+24640*v**6+25230*v**5+9639*v**4
            -480*v**3-1212*v*v-360*v-36, 3*v-1)


def assert_factorization(p, factors, powers):
    prod = p.context().constant(1)
    for f,e in zip(factors,powers):
        prod *= f**e
    assert not p.is_zero() and p == prod*(p.leading_coefficient()/prod.leading_coefficient())


def exceptional_cases():
    # If D=U=0 at either end, k=2-8g and q=8g²-8g+1, after reflection.
    at = (K(2)-8*g,8*g*g-8*g+1,g,y)
    assert not D.compose(*at) and not U.compose(*at)
    assert diag.compose(*at).degrees()[2] == 11
    assert anchor.compose(*at).degrees()[2] == 27
    assert diag.compose(*at).gcd(anchor.compose(*at)).is_constant()
    print("Both reflected D=0 branches: gcd 1", flush=True)

    # Symmetric k=0: any arithmetic end gives F and anchor; otherwise G and pin.
    sym = lambda p: p.subs({"k":0})
    assert strip(sym(A).gcd(sym(B)),sym(T)).is_constant()
    for p,h in ((F,anchor),(G,pin)):
        ps = [substitute_diagonal(sym(f),sym(B),180*sym(A)) for f in (p,h)]
        assert strip(ps[0].gcd(ps[1]),sym(T*A*B)).is_constant()
    print("Symmetric k=0: gcd 1 on every chronological branch", flush=True)

    # Exceptional A=B=0, k != 0: first solve for k² in each q fiber.
    fs = projection_factors(q)
    assert_factorization(A.resultant(B,"k"),fs,(2,2,2,0))
    a0,a2,a4 = coeffs(A,"k")[::2]
    b0,b2,b4 = coeffs(B,"k")[::2]
    dx,d0 = a4*b2-b4*a2,a4*b0-b4*a0
    for idx,f in enumerate(fs[:3]):
        fiber = Fiber(univar_q(f))
        xx = -d0*fiber.inv(dx % fiber.M) % fiber.M
        t0,t2 = coeffs(T,"k")[::2]
        tt = (t0+xx*t2) % fiber.M
        assert bool(tt) == (idx == 2)
        if not tt: continue
        assert xx

        def at_x(p):
            pars = []
            for part in parity(p):
                z = [fiber.zero for _ in range(1+part.degrees()[2])]
                for (a,b,j,h),v in part.terms():
                    assert a % 2 == 0 and not h
                    z[j] += (xx**(a//2) % fiber.M)*fmpq_poly([0]*b+[v])
                pars.append(fiber.clean(z))
            return pars

        fe,fo = at_x(F)
        ge,go = at_x(G)
        pe,po = at_x(pin)
        he,ho = at_x(anchor)

        def norm(a,b):
            return fiber.add(fiber.mul(a,a),[-xx*p for p in fiber.mul(b,b)])

        for polys in ((fe,fo,he,ho),(ge,go,pe,po),
                      (norm(fe,fo),norm(ge,go),norm(pe,po),norm(he,ho))):
            assert fiber.gcds(polys) == [fiber.one]
    print("A=B=0: two T=0 fibers; final fiber has gcd 1 in g", flush=True)


def ordinary_branch(branch):
    sub = lambda p: substitute_diagonal(p,B,180*A)
    gate = sub(R*mirror(R))*sub(D*mirror(D))*sub(U*mirror(U))*A*T*B*k
    two = fmpq_mpoly_ctx.get(("k","q"))
    kk,qq = two.gens()
    reflect = lambda p: p.compose(-kk,qq)
    f,gf,pin_f,h = [strip(sub(p),gate).project_to_context(two) for p in (F,G,pin,anchor)]
    gate = gate.project_to_context(two)

    if branch == "AZ":
        polys = [f,reflect(gf),reflect(pin_f),h]
        var = "k"
        powers = (36,27,18,1)
        fiber_degrees = (6,6,6,0)
    else:
        sq = fmpq_mpoly_ctx.get(("x","q"))
        def even(p):
            assert all(a % 2 == 0 for (a,_),_ in p.terms())
            return sq.from_dict({(a//2,b):c for (a,b),c in p.terms()})
        polys = []
        gate = gate*reflect(gate)
        for p in ((f,h) if branch == "AA" else (gf,pin_f)):
            polys.extend(even(strip(a,gate)) for a in ((p+reflect(p))/2,(p-reflect(p))/(2*kk)))
        gate = even(gate)
        var = "x"
        powers = (6,6,6,0) if branch == "AA" else (30,30,30,2)
        fiber_degrees = (2,2,2,0) if branch == "AA" else (5,5,5,0)

    common_projection = polys[0].context().constant(0)
    for p in polys[1:]:
        common_projection = common_projection.gcd(polys[0].resultant(p,var))
    factors = projection_factors(polys[0].context().gen(1))
    assert_factorization(common_projection,factors,powers)
    for f,e,deg in zip(factors,powers,fiber_degrees):
        if not e: continue
        fiber = Fiber(univar_q(f))
        common = fiber.gcds(coeffs(p,var) for p in polys)
        assert len(common)-1 == deg
        assert fiber.strip(common,coeffs(gate,var)) == [fiber.one]
    print(f"{branch}: projection multiplicities {powers}, no ungated fiber roots", flush=True)


if __name__ == "__main__":
    exceptional_cases()
    for branch in ("AA","AZ","ZZ"):
        ordinary_branch(branch)
