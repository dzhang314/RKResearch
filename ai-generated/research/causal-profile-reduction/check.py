#!/usr/bin/env python3
"""Independent small-field checks, not a search for physical tableaux."""
from itertools import product
from random import Random


def solve(rows, rhs, m, p):
    """RREF solution with free variables zero; also homogeneous null basis."""
    a = [[x % p for x in row] + [y % p] for row, y in zip(rows, rhs)]
    assert len(rows) == len(rhs) and all(len(r) == m + 1 for r in a)
    piv = []
    for j in range(m):
        i = len(piv)
        h = next((h for h in range(i, len(a)) if a[h][j]), None)
        if h is None:
            continue
        a[i], a[h] = a[h], a[i]
        u = pow(a[i][j], -1, p)
        a[i] = [u * t % p for t in a[i]]
        for h in range(len(a)):
            if h != i and a[h][j]:
                u = a[h][j]
                a[h] = [(t - u * v) % p for t, v in zip(a[h], a[i])]
        piv.append(j)
    null = []
    for j in range(m):
        if j not in piv:
            v = [0] * m
            v[j] = 1
            for i, h in enumerate(piv):
                v[h] = -a[i][j] % p
            null.append(v)
    if any(not any(row[:-1]) and row[-1] for row in a):
        return None, null
    v = [0] * m
    for i, h in enumerate(piv):
        v[h] = a[i][-1]
    return v, null


def comb(rows, target, p):
    return solve([[r[k] for r in rows] for k in range(len(target))],
                 target, len(rows), p)[0]


def pivots_relations(rows, order, p):
    piv, rel = [], {}
    for j in order:
        c = comb([rows[k] for k in piv], rows[j], p)
        if c is None:
            piv.append(j)
        else:
            v = [0] * len(rows)
            v[j] = 1
            for k, t in zip(piv, c):
                v[k] = -t % p
            rel[j] = v
    return piv, rel


def dot(x, y, p):
    return sum(a * b for a, b in zip(x, y)) % p


def causal(X, U, W, Z, p):
    n = len(X)
    front, f = pivots_relations(X, range(n), p)
    back, g = pivots_relations(U, reversed(range(n)), p)
    ix = [(i, j) for i in range(n) for j in range(i)]
    ns = [[g[i][h] * f[j][k] % p for h, k in ix]
          for i in g for j in f if j < i]
    N = [[0] * n for _ in range(n)]
    for i in range(n):
        cols = [j for j in front if j < i]
        c = comb([X[j] for j in cols], W[i], p)
        if c is None:
            return None, ns
        for j, t in zip(cols, c):
            N[i][j] = t
    for j in range(n):
        suffix = [i for i in back if i > j]
        c = comb([U[i] for i in suffix], Z[j], p)
        if c is None:
            return None, ns
        if j in f:
            for i, t in zip(suffix, c):
                N[i] = [(v + t * w) % p for v, w in zip(N[i], f[j])]
    if any(sum(U[i][b] * W[i][a] - Z[i][b] * X[i][a] for i in range(n)) % p
           for a in range(len(X[0])) for b in range(len(U[0]))):
        return None, ns
    return [N[i][j] for i, j in ix], ns


def dense(X, U, W, Z, p):
    n = len(X)
    ix = [(i, j) for i in range(n) for j in range(i)]
    rows, rhs = [], []
    for h in range(n):
        for a in range(len(X[0])):
            rows.append([X[j][a] if i == h else 0 for i, j in ix])
            rhs.append(W[h][a])
        for b in range(len(U[0])):
            rows.append([U[i][b] if j == h else 0 for i, j in ix])
            rhs.append(Z[h][b])
    return rows, rhs


def check_case(X, U, W, Z, p):
    n = len(X)
    m = n * (n - 1) // 2
    eq, rhs = dense(X, U, W, Z, p)
    ref, dense_null = solve(eq, rhs, m, p)
    sol, ns = causal(X, U, W, Z, p)
    assert (ref is None) == (sol is None)
    assert len(dense_null) == len(ns)
    if sol is not None:
        assert [dot(r, sol, p) for r in eq] == rhs
    assert all(not dot(r, v, p) for r in eq for v in ns)
    if ns:
        assert not solve(list(zip(*ns)), [0] * m, len(ns), p)[1]
    return sol is not None


def interpolation():
    counts = [0, 0]
    triples = list(product(range(2), repeat=3))
    for y, u, w, z in product(triples, repeat=4):
        wrap = lambda v: [[x] for x in v]
        ok = check_case(*map(wrap, [y, u, w, z]), 2)
        counts[ok] += 1
    print("GF(2), n=3, one feature each: exhaustive cases =", sum(counts),
          "(feasible =", counts[1], ")")
    rnd = Random(47831)
    counts = [0, 0]
    for p in (2, 5, 11):
        for n in (1, 3, 5, 8, 10):
            for h in range(18):
                a, b = rnd.randrange(1, 5), rnd.randrange(1, 5)
                mat = lambda r, c: [[rnd.randrange(p) for _ in range(c)] for _ in range(r)]
                X, U = mat(n, a), mat(n, b)
                if h % 3 == 0:  # Deliberate pivot delays.
                    for i in range(n // 2):
                        X[i] = X[0][:]
                        U[n - 1 - i] = U[-1][:]
                N = [[rnd.randrange(p) if j < i else 0 for j in range(n)]
                     for i in range(n)]
                W = [[sum(N[i][j] * X[j][k] for j in range(n)) % p
                      for k in range(a)] for i in range(n)]
                Z = [[sum(N[i][j] * U[i][k] for i in range(n)) % p
                      for k in range(b)] for j in range(n)]
                if h % 2:
                    Z[rnd.randrange(n)][rnd.randrange(b)] ^= 1
                    Z = [[v % p for v in row] for row in Z]
                ok = check_case(X, U, W, Z, p)
                counts[ok] += 1
    print("Additional interpolation cases =", sum(counts),
          "(feasible =", counts[1], ")")


def endpoint_identities():
    count = 0
    for p in (2, 3, 5, 11):
        for a, d, u in product(range(p), repeat=3):
            x, y = a, (d + u) % p
            s0, s1 = a * a % p, (2 * (u * x + d * y) - y * y) % p
            r10 = (y - x - a - d) * u % p
            t0, t1 = -a * a * x % p, (r10 * x - d * d * y) % p
            assert (s1 - (2*a*u + d*d - u*u)) % p == 0
            assert (t1 - (-2*a*a*u + a*u*u - d**3 - d*d*u)) % p == 0
            assert (s0*t1 - s1*t0 + a*a*d*d*(y-x)) % p == 0
            assert (u*s0 + d*s1 + t1 - u*(a-d)*(y-x)) % p == 0
            if a and d and x != y:
                assert (s0*t1 - s1*t0) % p
            count += 1
    print("Two-stage identities, exhaustive coefficient triples =", count)


def residual_packet():
    """Direct linear-algebra test of the homogeneous filtration reduction.

    Synthetic profiles only: no assumption of order in these fixtures.
    """
    rnd = Random(4417)
    p = 11
    checked = 0
    for n, order in ((8, 7), (10, 8)):
        for case in range(24):
            x = [rnd.randrange(p) for _ in range(n)]
            s = [rnd.randrange(p) for _ in range(n)]
            t = [rnd.randrange(p) for _ in range(n)]
            b = [rnd.randrange(1, p) for _ in range(n)]
            if case == 0:  # Force substantial testable homogeneous freedom.
                x[:] = [0] * n
                s[:] = [1] * n
            y = lambda k: [pow(v, k, p) for v in x]
            X = list(map(list, zip(y(0), y(1), y(2), s)))
            U = [[b[i] * v % p for v in X[i]] for i in range(n)]
            zero = [[0] * 4 for _ in range(n)]
            _, ns = causal(X, U, zero, zero, p)
            ix = [(i, j) for i in range(n) for j in range(i)]
            P = {0: [y(0)], 1: [y(0), y(1)], 2: [y(0), y(1), y(2), s],
                 3: [y(0), y(1), y(2), s, y(3), t]}
            D = {2: [s], 3: [s, t]}
            for k in range(4, order):
                tests = [[v * w % p for v, w in zip(u, b)]
                         for u in P[order - 1 - k]]
                D[k] = solve(tests, [0] * len(tests), n, p)[1]

            def pack(a, v):
                return [sum(a[i]*b[i]*H[k]*v[j] for k, (i, j) in enumerate(ix)) % p
                        for H in ns]

            full = []
            for k in range(3, order - 2):
                for a in P[order - 2 - k]:
                    for v in D[k]:
                        full.append(pack(a, v))
            for m in range(4, order - 1):
                for a in P[order - 1 - m]:
                    full.append(pack(a, y(m - 1)))
            small = [pack(a, v) for a in (y(3), t) for v in (y(3), t)] if order == 8 else []
            # All four variable pairings are explicitly in full at order eight;
            # the equality of kernels is checked without assuming rank four.
            _, nf = solve(full, [0] * len(full), len(ns), p)
            _, nsml = solve(small, [0] * len(small), len(ns), p)
            assert len(nf) == len(nsml)
            assert all(not dot(r, v, p) for r in full for v in nsml)
            assert all(not dot(r, v, p) for r in small for v in nf)
            checked += 1
    print("Full advance/primitive homogeneous kernels vs cubic packet =", checked)


if __name__ == "__main__":
    interpolation()
    endpoint_identities()
    residual_packet()
    print("All checks pass. No tableau attainment is inferred.")
