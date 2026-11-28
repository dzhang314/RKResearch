#!/usr/bin/env python3
"""Independent exact midpoint primitive-profile replay, even orders 2..20."""
from fractions import Fraction as Q
from math import comb, factorial, lcm, prod
from pathlib import Path
import json


def midpoint_primitive(d):
    """Coefficient for h^(2*k)*X^(d+1-2*k), k in increasing order."""
    u = []
    for k in range(d // 2 + 1):
        remainder = Q(k == 0) - sum(
            u[j] * Q(comb(d + 1 - 2*j, 2*(k-j) + 1), 4**(k-j))
            for j in range(k)
        )
        u.append(remainder / (d + 1 - 2*k))
    # Independent centered-difference check on every homogeneous coefficient.
    for k in range(d // 2 + 1):
        entry = sum(
            u[j] * Q(comb(d + 1 - 2*j, 2*(k-j) + 1), 4**(k-j))
            for j in range(k+1)
        )
        assert entry == (k == 0)
    return u


def replay(r):
    p = 2*r
    branches = list(range(1, r+1))
    sizes = [(m, j) for m in branches for j in range(m)]
    s = len(sizes)
    assert s == r*(r+1)//2
    steps = [Q(1, m) for m, _ in sizes]
    clocks = [Q(2*j+1, 2*m) for m, j in sizes]
    lambdas = {
        m: prod(Q(1) / (1 - Q(l*l, m*m)) for l in branches if l != m)
        for m in branches
    }
    assert all(sum(lambdas[m] * Q(1, m*m)**g for m in branches) == (g == 0)
               for g in range(r))
    weights = [lambdas[m]*h for (m, _), h in zip(sizes, steps, strict=True)]
    mat = [[
        h if m == n and j > k else h/2 if m == n and j == k else Q(0)
        for (n,k), h in zip(sizes, steps, strict=True)]
        for m,j in sizes]
    rows = [[(j, a) for j, a in enumerate(row) if a] for row in mat]

    def act(v):
        return [sum(a * v[j] for j, a in row) for row in rows]

    def read(v):
        return sum(w*x for w,x in zip(weights, v, strict=True))

    assert act([Q(1)]*s) == clocks
    assert all(not a for i, row in enumerate(mat) for j, a in enumerate(row) if i < j)
    if r >= 2:
        assert mat[0][0] == Q(1,2) and mat[1][1] == Q(1,4)
    u = [h*h for h in steps]
    for i, row in enumerate(rows):
        assert all(u[i] == u[j] for j, _ in row)
    assert [2*a - c*c for a,c in zip(act(clocks),clocks, strict=True)] == [v/4 for v in u]

    for d in range(p-1):
        primitive = midpoint_primitive(d)
        coeff = [
            (d+1) * sum(
                primitive[j] * Q(comb(d+1-2*j, 2*(k-j)), 4**(k-j))
                for j in range(min(k+1,len(primitive)))
            )
            for k in range((d+1)//2+1)
        ]
        assert coeff[0] == 1
        expect = [
            sum(a * v**k * c**(d+1-2*k) for k,a in enumerate(coeff))
            for v,c in zip(u,clocks,strict=True)
        ]
        assert [(d+1)*v for v in act([c**d for c in clocks])] == expect

    for k in range(r):
        for d in range(p-2*k):
            assert read([v**k*c**d for v,c in zip(u,clocks,strict=True)]) == (
                Q(1,d+1) if not k else Q(0)
            )

    v = [Q(1)]*s
    for _ in range(p):
        v = act(v)
    defect = factorial(p+1)*read(v)-1
    assert defect == Q((-1)**(r+1)*comb(2*r,r), 4**r)
    assert factorial(p) % abs(defect.numerator) == 0
    assert factorial(p)**2 % defect.denominator == 0
    D = lcm(*(a.denominator for row in mat for a in row),
            *(b.denominator for b in weights))
    exponent = next(k for k in range(1,p+2) if factorial(p)**k % D == 0)
    if r == 6:
        literal = json.loads(Path(__file__).with_name("tableau21.json").read_text())
        assert mat == [[Q(a) for a in row] for row in literal["A"]]
        assert weights == list(map(Q,literal["b"]))
        assert clocks == list(map(Q,literal["c"]))
        assert str(defect) == literal["thirteenth_tall_defect"]
    print(f"order {p:2d}: width {s:2d}, D={D}, D | ({p}!)^{exponent}, next tall={defect}")


if __name__ == "__main__":
    for r in range(1, 11):
        replay(r)
