#!/usr/bin/env python3
"""Independent replay of the exact continuous-pencil determinant receipts."""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, isqrt
from pathlib import Path
import json

J5 = (-1, 35, -280, 840, -1050, 462)
J6 = (1, -48, 540, -2400, 4950, -4752, 1716)
MODULI = (1009, 1013)


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def evaluate(poly, u, p):
    return sum(c * pow(u, i, p) for i, c in enumerate(poly)) % p


def mod_gcd(f, g, p):
    while g:
        r = list(f)
        inv = pow(g[-1], -1, p)
        while r and len(r) >= len(g):
            pos = len(r) - len(g)
            v = r[-1] * inv % p
            for j, c in enumerate(g):
                r[pos + j] = (r[pos + j] - v * c) % p
            while r and r[-1] == 0:
                r.pop()
        f, g = g, r
    inv = pow(f[-1], -1, p)
    return [v * inv % p for v in f]


def determinant(matrix, p):
    """Modular elimination with normalized pivot row and a sign ledger."""
    a = [list(row) for row in matrix]
    value = 1
    for j in range(len(a)):
        try:
            r = next(i for i in range(j, len(a)) if a[i][j])
        except StopIteration:
            return 0
        if r != j:
            a[j], a[r] = a[r], a[j]
            value = -value
        pivot = a[j][j]
        value = value * pivot % p
        inv = pow(pivot, -1, p)
        row = [c * inv % p for c in a[j][j+1:]]
        for i in range(j+1, len(a)):
            d = a[i][j]
            a[i][j+1:] = [(c - d * q) % p for c, q in zip(a[i][j+1:], row)]
    return value % p


def divided_coefficients(u, p):
    # Expand the alternating quotient monomial by monomial, not synthetic division.
    q = [0] * 6
    for i, a in enumerate(J6):
        for j, b in enumerate(J5):
            c = a * b
            if i < j:
                first, last, sign = i, j, -1
            elif i > j:
                first, last, sign = j, i, 1
            else:
                continue
            for k in range(first, last):
                q[k] = (q[k] + sign * c * pow(u, i+j-1-k, p)) % p
    return q


def both_compound_dets(u, degree, p):
    sites = list(combinations(range(5), degree))
    q = divided_coefficients(u, p)
    const = [[(q[i] if j == 4 else -int(i == j+1)) % p
              for j in range(5)] for i in range(5)]
    linear = [u % p] * 4 + [u * q[5] % p]
    integrals = [[pow(a+j+1, -1, p) for j in range(degree+1)] for a in (0, 1)]
    traces = [[], []]
    terms = []
    for perm in permutations(range(degree)):
        sign = (-1)**sum(perm[i] > perm[j] for i in range(degree) for j in range(i+1, degree))
        terms.append((perm, sign))
    for rows in sites:
        entries = [[], []]
        for cols in sites:
            # Leibniz expansion in the integration variable, with exact monomial integrals.
            minor = [0] * (degree+1)
            for perm, sign in terms:
                h = [sign]
                for i, rank in zip(rows, perm):
                    j = cols[rank]
                    z, v = const[i][j], linear[j] if i == j else 0
                    new = [0] * (len(h)+1)
                    for k, old in enumerate(h):
                        new[k] += z * old
                        new[k+1] += v * old
                    h = new
                for k, v in enumerate(h):
                    minor[k] += v
            for a in (0, 1):
                entries[a].append(sum(h*w for h, w in zip(minor, integrals[a])) % p)
        for trace, row in zip(traces, entries):
            trace.append(row)
    return [determinant(trace, p) for trace in traces]


def main():
    for f in (J5, J6):
        require(all(sum(Fraction(c, (i+j+1)*(i+j+2)) for i, c in enumerate(f)) == 0
                    for j in range(len(f)-1)), ("Jacobi moment", f))
    for p in MODULI:
        require(all(p % d for d in range(2, isqrt(p)+1)), ("modulus not prime", p))
    require(mod_gcd([c % 1009 for c in J5], [c % 1009 for c in J6], 1009) == [1],
            "Jacobi generators share a root")
    rows = [json.loads(s) for s in Path(__file__).with_name("expanded.jsonl").read_text().splitlines()]
    require([(r["pr"], r["k"]) for r in rows] == [(p, k) for p in MODULI for k in (2, 3)],
            "exact scope of receipt")
    for row in rows:
        p, k, cap = row["pr"], row["k"], row["cap"]
        polys = row["cs"]
        require(cap == 2*k*comb(5, k) and p > cap+3, ("degree budget", p, k))
        require(len(polys) == 2 and all(len(f) == cap+1 and f[-1] and
                all(0 <= x < p for x in f) for f in polys), ("degree preservation", p, k))
        require([f[-1] for f in polys] == row["lc"], ("leading coefficient", p, k))
        for u in range(cap+3):
            got = both_compound_dets(u, k, p)
            require(got == [evaluate(f, u, p) for f in polys], ("determinant", p, k, u))
        require(mod_gcd(*polys, p) == row["gcd"] == [1], ("gcd", p, k))
        print(f"p={p}; exterior degree={k}; polynomial degrees={cap},{cap}; evaluations={cap+3}; gcd=1")
    print("Jacobi moments and consecutive gcd verified.")


if __name__ == "__main__":
    main()
