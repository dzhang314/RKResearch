#!/usr/bin/env python3
"""Exact, standalone scope counterexample; no floating point or Lean.

Tree recursion is precisely RKResearch.Φ and factorial on unordered
child tuples. Polynomial arithmetic is in Q[T]/g with evaluation at
a bracketed real root, and sign checks are rational Horner intervals.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import prod


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def plus(p, q):
    p, q = tuple(p), tuple(q)
    n = max(len(p), len(q))
    return trim((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                for i in range(n))


def scale(p, a):
    return trim(a * b for b in p)


def times(p, q):
    if not p or not q:
        return ()
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def divmod_q(p, q):
    """Euclidean division in Q[T] only."""
    assert q
    d = ()
    while p and len(p) >= len(q):
        u = (Q(0),) * (len(p) - len(q)) + (p[-1] / q[-1],)
        d = plus(d, u)
        p = plus(p, scale(times(q, u), -1))
    return d, p


G = tuple(map(Q, (4, -30, 95, -120, 50)))
LOW, HIGH = Q(773087032049, 10**12), Q(773087032050, 10**12)


def ev(p, x):
    v = 0
    for a in reversed(p):
        v = v * x + a
    return v


def enclosure(p):
    lo = hi = Q(0)
    for a in reversed(p):
        values = (lo * LOW, lo * HIGH, hi * LOW, hi * HIGH)
        lo, hi = min(values) + a, max(values) + a
    return lo, hi


@lru_cache(None)
def invert(p):
    assert p
    a, b = G, p
    u, v = (), (Q(1),)
    while b:
        w, r = divmod_q(a, b)
        a, b = b, r
        u, v = v, plus(u, scale(times(w, v), -1))
    assert len(a) == 1
    w = divmod_q(scale(u, 1 / a[0]), G)[1]
    assert divmod_q(times(p, w), G)[1] == (Q(1),)
    return w


class Exact:
    __slots__ = ("p",)

    def __init__(self, n=0):
        if isinstance(n, Exact):
            self.p = n.p
        else:
            self.p = divmod_q(trim(map(Q, n if isinstance(n, tuple) else (n,))), G)[1]

    def __eq__(self, other):
        return self.p == Exact(other).p

    def __add__(self, other):
        return Exact(plus(self.p, Exact(other).p))

    __radd__ = __add__

    def __neg__(self):
        return Exact(scale(self.p, -1))

    def __sub__(self, other):
        return self + (-Exact(other))

    def __rsub__(self, other):
        return Exact(other) + (-self)

    def __mul__(self, other):
        return Exact(times(self.p, Exact(other).p))

    __rmul__ = __mul__

    def __truediv__(self, other):
        return self * Exact(invert(Exact(other).p))

    def __rtruediv__(self, other):
        return Exact(other) / self

    def __pow__(self, n):
        assert n >= 0
        a, x = Exact(1), self
        while n:
            if n & 1:
                a = a * x
            n //= 2
            x = x * x
        return a

    def positive(self):
        return enclosure(self.p)[0] > 0

    def __repr__(self):
        return f"Exact{self.p}"


ZERO, ONE, t = Exact(0), Exact(1), Exact((0, 1))


def close(x, lo, hi):
    assert (x - lo).positive() and (hi - x).positive(), (x, lo, hi, enclosure(x.p))


def integral(p, z=ONE):
    return sum(v * z**(k + 1) / (k + 1) for k, v in enumerate(p))


def lin(c):
    return (-c, ONE)


def collocation(c):
    result = []
    for j, x in enumerate(c):
        basis = (ONE,)
        for k, y in enumerate(c):
            if k != j:
                basis = times(basis, lin(y))
        result.append(scale(basis, 1 / ev(basis, x)))
    assert tuple(map(sum, zip(*result))) == (ONE, ZERO, ZERO, ZERO)
    assert tuple(tuple(ev(L, x) for L in result) for x in c) == tuple(
        tuple(ONE if i == j else ZERO for j in range(len(c))) for i in range(len(c)))
    return (tuple(tuple(integral(L, x) for L in result) for x in c),
            tuple(integral(L) for L in result))


def tree_table(p):
    """Canonical sorted child tuples, every multiset of total size n-1."""
    tab = {1: ((),)}
    for n in range(2, p + 1):
        children = [(m, child) for m in range(1, n) for child in tab[m]]

        def forests(first, weight):
            if weight == 0:
                yield ()
                return
            for i in range(first, len(children)):
                size, child = children[i]
                if size > weight:
                    break
                for rest in forests(i, weight - size):
                    yield (child,) + rest

        tab[n] = tuple(forests(0, n - 1))
        assert len(tab[n]) == len(set(tab[n]))
    return tab


@lru_cache(None)
def size(tree):
    return 1 + sum(map(size, tree))


@lru_cache(None)
def factorial(tree):
    return size(tree) * prod(map(factorial, tree))


def check_order(A, b, clocks):
    sparse = tuple(tuple((j, a) for j, a in enumerate(row) if a != 0) for row in A)

    @lru_cache(None)
    def phi(tree):
        children = tuple(map(phi, tree))
        return tuple(prod(sum(a * values[j] for j, a in row)
                          for values in children) for row in sparse)

    c = tuple(map(sum, A))
    assert c == clocks
    trees = tree_table(6)
    assert tuple(map(len, trees.values())) == (1, 1, 2, 4, 9, 20)
    for n, ts in trees.items():
        for tree in ts:
            assert size(tree) == n
            assert factorial(tree) * sum(v * w for v, w in zip(b, phi(tree))) == 1, tree
    assert sum(bi * ci**6 for bi, ci in zip(b, c)) != Q(1, 7)
    return sum(map(len, trees.values()))


def lower_triangular_lift(A, b, c, gamma, p=6):
    """One gamma ghost then p-1 successive blocks, final block visible."""
    assert p >= 2
    n = len(c)
    nblocks, nrows = p - 1, 1 + n * (p - 1)
    lifted = [[ZERO] * nrows for _ in range(nrows)]
    for k in range(nrows):
        lifted[k][k] = gamma
    for k, ck in enumerate(c):
        lifted[k + 1][0] = ck - gamma
    for block in range(1, nblocks):
        for i in range(n):
            for j in range(n):
                lifted[1 + n * block + i][1 + n * (block - 1) + j] = (
                    A[i][j] - (gamma if i == j else ZERO))
    weights = (ZERO,) * (nrows - n) + b
    assert all(lifted[i][j] == 0 for i in range(nrows) for j in range(i + 1, nrows))
    assert all(lifted[i][i] == gamma for i in range(nrows))
    return lifted, weights, (gamma,) + c * nblocks


def check_join_case(label, c, gamma, reflected, alpha, s):
    seed, b = collocation(c)
    assert check_order(seed, b, c) == 37
    A, b, c = lower_triangular_lift(seed, b, c, gamma)
    assert check_order(A, b, c) == 37
    assert len(set(x.p for x in c)) == 4
    assert all((x == 0 or x.positive()) and (x == 1 or (1 - x).positive()) for x in c)
    assert all(bi == 0 or bi.positive() for bi in b)
    assert sum(bi != 0 for bi in b) == 4
    assert gamma == 0 or gamma.positive()
    n = len(c)
    assert n == 21
    z = tuple(1 - x if reflected else x for x in c)
    at = tuple(i for i in range(n) if z[i] == t)
    assert at and sum(b[i] for i in at).positive() and len(at) > 1
    assert sum(b[i] != 0 for i in at) == 1
    oriented_eval = tuple(x - alpha for x in z)
    diag = sum(b[i] * A[i][i] * oriented_eval[i] for i in at)
    if reflected:
        strict = sum(b[j] * A[j][i] * oriented_eval[j] for i in at for j in range(i + 1, n))
    else:
        strict = sum(b[i] * A[i][j] * oriented_eval[j] for i in at for j in range(i))
    assert strict + diag == 0
    assert (diag.positive() and (-strict).positive()) if gamma != 0 else (diag == strict == 0)

    def mass(x):
        return sum(bi * (1 - zi) * (zi - alpha) for bi, zi in zip(b, z) if zi == x)

    mu_s, mu_t = mass(s), mass(t)
    assert (-mu_s).positive() and mu_t.positive()
    assert mass(alpha) == mass(ONE) == 0
    fH = times((ONE, -ONE), lin(alpha))
    for k in range(4):
        physical_sum = sum(bi * ev(fH, zi) * zi**k for bi, zi in zip(b, z))
        assert physical_sum == mu_s * s**k + mu_t * t**k
        assert physical_sum == integral((ZERO,) * k + fH)
    assert integral(lin(alpha), t) == 0
    S = mu_s / (1 - s)
    J = mu_t / (1 - t)
    assert (-S).positive() and (S + J).positive()
    print(f"{label}: 21 stages; 4 physical clocks; 37 exact lifted trees; order 7 fails via bush")
    print(f"  actual grouped {('reflected suffix' if reflected else 'prefix')} numerator = 0; "
          "physical lifted masses on {s,t}, stop mass > 0; degree-3 law exact")
    print(f"  diagonal part {'positive' if gamma != 0 else 'zero'}; strict part "
          f"{'negative' if gamma != 0 else 'zero'}; S < 0 < S + J")


def main():
    gl, gh = ev(G, LOW), ev(G, HIGH)
    assert gl > 0 > gh
    s = (10 * t**2 - 15 * t + 6) / (30 * t**2 - 30 * t + 10)
    alpha = t / 2
    close(s, Q(80, 1000), Q(81, 1000))
    close(alpha, Q(386, 1000), Q(387, 1000))
    c = (s, alpha, t, ONE)
    nodal = (ONE,)
    for x in c:
        nodal = times(nodal, lin(x))
    assert integral(nodal) == integral((ZERO,) + nodal) == 0
    rho = integral((ZERO, ZERO) + nodal)
    assert rho == -Q(1, 532) + Q(3, 380)*t - Q(7, 570)*t**2 + t**3/152
    close(rho, Q(-77, 10**6), Q(-76, 10**6))
    _, b = collocation(c)
    boxes = ((202, 203), (383, 385), (346, 347), (67, 69))
    for bi, (l, r) in zip(b, boxes):
        close(bi, Q(l, 1000), Q(r, 1000))
    for k in range(6):
        assert sum(bi * ci**k for bi, ci in zip(b, c)) == Q(1, k + 1)
    print("t bracket = (773087032049, 773087032050)/10^12; quartic signs +,- checked exactly")
    print("quadrature exact through degree 5; degree-6 nodal witness in (-77,-76)/10^6")
    print("four quadrature weights lie in open 10^-3 boxes", boxes)

    check_join_case("positive common-diagonal SDIRK", c, t, False, alpha, s)
    c_reflection = tuple(1 - x for x in reversed(c))
    check_join_case("strict ERK", c_reflection, ZERO, True, alpha, s)
    check_join_case("positive common-diagonal SDIRK reflected", c_reflection, 1 - t, True, alpha, s)


if __name__ == "__main__":
    main()
