#!/usr/bin/env python3
"""Exact supplementary regression in Q(sqrt(15)); the proof is in the note.

The small instance exercises a genuinely nonzero changed same-row diagonal
child term. It regenerates its own data and no earlier tableau is imported.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import cache
from math import prod


@dataclass(frozen=True)
class K:
    a: Q = Q(0)
    b: Q = Q(0)

    @staticmethod
    def coerce(x):
        return x if isinstance(x, K) else K(Q(x))

    def __add__(self, x):
        x = self.coerce(x)
        return K(self.a + x.a, self.b + x.b)

    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b)

    def __sub__(self, x):
        return self + -self.coerce(x)

    def __rsub__(self, x):
        return self.coerce(x) + -self

    def __mul__(self, x):
        x = self.coerce(x)
        return K(self.a * x.a + 15 * self.b * x.b,
                 self.a * x.b + self.b * x.a)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = self.coerce(x)
        norm = x.a * x.a - 15 * x.b * x.b
        return self * K(x.a / norm, -x.b / norm)

    def __pow__(self, n):
        assert n >= 0
        result = ONE
        for _ in range(n):
            result *= self
        return result

    def sign(self):
        a, b = self.a, self.b
        sign = lambda q: (q > 0) - (q < 0)
        if not a or not b or sign(a) == sign(b):
            return sign(a or b)
        return sign(a) * sign(a * a - 15 * b * b)


ZERO, ONE = K(), K(Q(1))
P, N = 6, 3
CLOCKS = (K(Q(1, 2), Q(-1, 10)), K(Q(1, 2)), K(Q(1, 2), Q(1, 10)))
WEIGHTS = tuple(map(K.coerce, (Q(5, 18), Q(4, 9), Q(5, 18))))


def poly_mul(p, q):
    result = [ZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return result


def basis(nodes, t):
    p, scale = [ONE], ONE
    for u in nodes:
        if u != t:
            p = poly_mul(p, [-u, ONE])
            scale *= t - u
    return [a / scale for a in p]


def evaluate(p, t, primitive=False):
    return sum((a * t ** (j + int(primitive)) / (j + 1 if primitive else 1)
                for j, a in enumerate(p)), ZERO)


def barycentric(nodes):
    return {x: ONE / prod((x - y for y in nodes if y != x), start=ONE)
            for x in nodes}


@cache
def order(tree):
    return 1 + sum(map(order, tree))


@cache
def factorial(tree):
    return order(tree) * prod(map(factorial, tree))


def tree_list(p):
    by_degree = [(), ((),)]
    for degree in range(2, p + 1):
        available = tuple(t for block in by_degree for t in block)

        def forests(left, start):
            if not left:
                yield ()
            for i in range(start, len(available)):
                t = available[i]
                if order(t) <= left:
                    for tail in forests(left - order(t), i):
                        yield (t,) + tail

        by_degree.append(tuple(forests(degree - 1, 0)))
    assert [len(block) for block in by_degree[1:]] == [1, 1, 2, 4, 9, 20]
    return tuple(t for block in by_degree for t in block)


TREES = tree_list(P)
GAUSS = [[evaluate(basis(CLOCKS, t), u, primitive=True) for t in CLOCKS]
         for u in CLOCKS]


def tableau(gamma, sites):
    rows = [{0: gamma}]

    def append(row):
        rows.append({**row, len(rows): gamma})
        return len(rows) - 1

    prev = (0,)
    nodes = (gamma,)
    for grade in range(2, P):
        new = sites if grade == P - 1 else tuple(K.coerce(j + 2) for j in range(grade))
        polynomials = [basis(nodes, t) for t in nodes]
        prev = tuple(append({i: evaluate(q, x, primitive=True) - gamma * evaluate(q, x)
                             for i, q in zip(prev, polynomials)}) for x in new)
        nodes = new
    donors = dict(zip(sites, prev))
    prev = tuple(append({}) for _ in CLOCKS)
    for _ in range(P):
        prev = tuple(append({i: GAUSS[k][j] - (gamma if k == j else ZERO)
                             for j, i in enumerate(prev)}) for k in range(N))
    return rows, donors, prev


def responses(rows):
    def action(i, v):
        return sum((a * v[j] for j, a in rows[i].items()), ZERO)

    @cache
    def phi(tree):
        if not tree:
            return (ONE,) * len(rows)
        children = tuple(map(phi, tree))
        return tuple(prod((action(i, v) for v in children), start=ONE)
                     for i in range(len(rows)))
    return phi, action


def check(gamma, degree, stops):
    nu, r = P - degree, P - degree - N - 1
    hidden = tuple(K(Q(j + 1, 11)) for j in range(r + len(stops) + 1))
    sites = tuple(u for u in CLOCKS if u not in stops) + hidden
    assert len(set(sites)) == nu and not set(hidden) & set(CLOCKS)
    w, beta = barycentric(sites), barycentric(CLOCKS[:degree + 1])
    alpha = {u: beta.get(u, ZERO) / b for u, b in zip(CLOCKS, WEIGHTS)}
    assert all(sum((w[x] * x ** k for x in sites), ZERO) == ZERO for k in range(nu - 1))
    assert all(sum((beta[u] * u ** k for u in beta), ZERO) == (ONE if k == degree else ZERO)
               for k in range(degree + 1))
    base, donors, live = tableau(gamma, sites)
    changed = [row.copy() for row in base]
    for i, u in zip(live, CLOCKS):
        for x, donor in donors.items():
            assert donor < i and donor not in changed[i]
            changed[i][donor] = alpha[u] * w[x]
    c = tuple(sum(row.values(), ZERO) for row in changed)
    assert c == tuple(sum(row.values(), ZERO) for row in base)
    assert tuple(c[i] for i in live) == CLOCKS and all(c[i] == x for x, i in donors.items())
    assert all(row[i] == gamma and all(j <= i for j in row) for i, row in enumerate(changed))
    old_phi, old_action = responses(base)
    new_phi, new_action = responses(changed)
    diagonal_path = False
    for tree in TREES:
        old, new = old_phi(tree), new_phi(tree)
        assert factorial(tree) * sum((b * old[i] for i, b in zip(live, WEIGHTS)), ZERO) == ONE
        assert factorial(tree) * sum((b * new[i] for i, b in zip(live, WEIGHTS)), ZERO) == ONE
        if order(tree) < P:
            ff = factorial(tree) // order(tree)
            assert all(old[i] == new[i] == x ** (order(tree) - 1) / ff for x, i in donors.items())
        affected = [tau for tau in tree if order(tau) >= nu]
        assert len(affected) <= 1
        if not affected:
            assert all(new[i] == old[i] for i in live)
        for tau in tree:
            v, vp = old_phi(tau), new_phi(tau)
            for i, u in zip(live, CLOCKS):
                diagonal = gamma * (vp[i] - v[i])
                direct = sum((alpha[u] * w[x] * v[j] for x, j in donors.items()), ZERO)
                assert new_action(i, vp) - old_action(i, v) == diagonal + direct
                if order(tau) < nu:
                    assert diagonal == direct == ZERO
                if diagonal != ZERO:
                    diagonal_path = True
    next_bush = ((),) * P
    assert (P + 1) * sum((b * new_phi(next_bush)[i] for i, b in zip(live, WEIGHTS)), ZERO) != ONE

    def column(rows, x, degree):
        return sum((b * u ** degree * a
                    for i, b, u in zip(live, WEIGHTS, CLOCKS)
                    for j, a in rows[i].items() if c[j] == x), ZERO)

    off = set(c) - set(CLOCKS)
    assert all(column(base, h, degree) == ZERO for h in off)
    assert {h for h in off if column(changed, h, degree) != ZERO} == set(hidden)
    assert all(column(changed, h, degree) == w[h] for h in hidden)
    for u, b in zip(CLOCKS, WEIGHTS):
        for k in range(degree + 1):
            value = b * (ONE - u ** (k + 1)) / (k + 1)
            assert column(base, u, k) == value
            assert (column(changed, u, k) == value) == (u in stops or k < degree)
    tilted = [column(changed, h, degree) * prod((h - u for u in CLOCKS if u not in stops), start=ONE)
              for h in hidden]
    assert all(sum((w0 * h ** k for h, w0 in zip(hidden, tilted)), ZERO) == ZERO
               for k in range(r + len(stops)))
    assert all(a.sign() * b.sign() < 0 for a, b in zip(tilted, tilted[1:]))
    assert diagonal_path == (gamma != ZERO and degree == 2)
    return diagonal_path


if __name__ == '__main__':
    cases = diagonal_hits = 0
    for gamma in (ZERO, K(Q(1, 7))):
        for degree in range(3):
            for stops in ((), CLOCKS[1:2], CLOCKS):
                diagonal_hits += int(check(gamma, degree, stops))
                cases += 1
    print(f'Exact Q(sqrt(15)): {cases} strict ERK/SDIRK variations, {len(TREES)} paid trees each')
    print(f'Actual nonzero same-row diagonal child difference exercised in {diagonal_hits} variations')
    print('Gauss clocks and weights fixed; next bush fails in every variant')
    print('Exact hidden support, zero-charge subset, and tilted alternation verified')
