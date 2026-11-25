#!/usr/bin/env python3
"""Independent exact checks of actual rooted order and the loss ledger."""

from fractions import Fraction as F
from functools import cache
from math import factorial, prod


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(p, q):
    r = [F(0)] * max(len(p), len(q))
    for a in (p, q):
        for i, a_i in enumerate(a):
            r[i] += a_i
    return trim(r)


def scale(p, c):
    return trim(c * p_i for p_i in p)


def mul(p, q):
    r = ()
    for i, p_i in enumerate(p):
        r = add(r, (F(0),) * i + scale(q, p_i))
    return r


def divmod_poly(p, q):
    assert q
    s = [F(0)] * max(0, len(p) - len(q) + 1)
    while p and len(p) >= len(q):
        i = len(p) - len(q)
        c = p[-1] / q[-1]
        s[i] = c
        p = add(p, (F(0),) * i + scale(q, -c))
    return trim(s), p


def divide(p, q):
    quo, rem = divmod_poly(p, q)
    assert not rem, (p, q, rem)
    return quo


def gcd(p, q):
    while q:
        p, q = q, divmod_poly(p, q)[1]
    assert p and p[0]
    return scale(p, 1 / p[0])


def integral_at(p, x):
    return sum((p_i * x**(i + 1) / (i + 1) for i, p_i in enumerate(p)), F(0))


def lagrange(nodes, i):
    l_i = (F(1),)
    for j, x_j in enumerate(nodes):
        if i != j:
            l_i = mul(l_i, (-x_j, F(1)))
            l_i = scale(l_i, 1 / (nodes[i] - x_j))
    return l_i


@cache
def size(tree):
    return 1 + sum(map(size, tree))


@cache
def tree_factorial(tree):
    return size(tree) * prod(map(tree_factorial, tree))


@cache
def trees(n):
    if n == 1:
        return ((),)
    pool = tuple(t for k in range(1, n) for t in trees(k))

    def forests(rem, lo):
        if rem == 0:
            yield ()
        else:
            for i in range(lo, len(pool)):
                t = pool[i]
                if size(t) > rem:
                    break
                for tail in forests(rem - size(t), i):
                    yield (t,) + tail

    return tuple(forests(n - 1, 0))


def dot(row, vector):
    return sum((a * v for a, v in zip(row, vector)), F(0))


def apply(A, v):
    return tuple(sum((a * v[j] for j, a in row.items()), F(0)) for row in A)


def exact_full_order(A, b, p):
    @cache
    def phi(tree):
        factors = [apply(A, phi(t)) for t in tree]
        return tuple(prod(f[i] for f in factors) for i in range(len(A)))

    count = 0
    for n in range(1, p + 1):
        for t in trees(n):
            assert dot(b, phi(t)) == F(1, tree_factorial(t)), (p, t)
            count += 1
    tall = ()
    for _ in range(p):
        tall = (tall,)
    assert dot(b, phi(tall)) - F(1, factorial(p + 1)) == F(1, p * factorial(p + 1))
    return count


def seed(p):
    gam = F(1, p)
    nodes = tuple(map(F, range(2, p + 2)))
    basis = tuple(lagrange(nodes, j) for j in range(p))
    A = [{}, {0: gam, 1: gam}]
    for x in nodes:
        a = x*x / (4*gam)
        A.append({0: x - a, 1: a})
    for ell in range(2, p - 1):
        lo = 2 + (ell - 2) * p
        for x in nodes:
            A.append({lo + j: integral_at(L, x) for j, L in enumerate(basis)})
    b = [F(0)] * (len(A) - p) + [integral_at(L, F(1)) for L in basis]
    assert all(b[-p:])
    return A, b


def append(A, b, p, lam, live):
    if live:
        taps = tuple(map(F, range(p + 10, 2*p + 11)))
        w = [1 / prod(t - u for u in taps if t != u) for t in taps]
        assert len(taps) == p + 1 and all(w)
        assert [dot(w, [t**k for t in taps]) for k in range(p + 1)] == [0]*p + [1]
    else:
        taps, w = (F(p+10),), [F(0)]
    return A + [{0: t, len(A) + j: lam} for j, t in enumerate(taps)], b + w


def characteristic_response(A, ell, e):
    """Compute the actual unreduced D,N by forward substitution, not a fit."""
    labels = {row.get(i, F(0)) for i, row in enumerate(A)} - {0}
    di = tuple(trim((F(1), -row.get(i, F(0)))) for i, row in enumerate(A))
    D = (F(1),)
    for d in di:
        D = mul(D, d)
    U = []  # U_i = D * ((I-XA)^(-1)e)_i.
    N = D
    for i, row in enumerate(A):
        a = ()
        for j, a_ij in row.items():
            assert j <= i
            if j < i:
                a = add(a, scale(U[j], a_ij))
        U.append(divide(add(scale(D, e[i]), (F(0),) + a), di[i]))
        N = add(N, (F(0),) + scale(U[-1], ell[i]))
    return D, N, labels


def ledger(A, ell, e, retained_labels):
    D, N, labels = characteristic_response(A, ell, e)
    C = gcd(D, N)
    P, Q = divide(N, C), divide(D, C)
    assert retained_labels <= labels
    return (D, N, P, Q, labels), (len(C) - 1, len(A) + 1 - len(N), len(labels - retained_labels))


def quotient_by_line(A, b, q):
    """Use coordinates v_i - q_i v_k / q_k, i≠k, on the actual quotient."""
    k = next(i for i, q_i in enumerate(q) if q_i)
    keep = tuple(i for i in range(len(A)) if i != k)
    f = [q_i / q[k] for q_i in q]
    Aprime = [
        {jj: A[i].get(j, 0) - f[i]*A[k].get(j, 0) for jj, j in enumerate(keep)
         if A[i].get(j, 0) - f[i]*A[k].get(j, 0)}
        for i in keep
    ]
    ellprime = [b[i] for i in keep]
    eprime = [1 - f[i] for i in keep]
    assert dot(b, q) == 0
    return Aprime, ellprime, eprime


def check(p):
    gam = F(1, p)
    A, b = seed(p)
    e = [F(1)] * len(A)
    c = apply(A, e)
    assert tuple(2*x for x in apply(A, c)) == tuple(x*x for x in c)
    total = exact_full_order(A, b, p)
    base, loss0 = ledger(A, b, e, {gam})
    D0, N0, P0, Q0, labels0 = base
    assert Q0 == (F(1), -gam)
    assert P0 == tuple(F(1 - j*gam, factorial(j)) for j in range(p))
    assert (D0, N0, labels0) == (Q0, P0, {gam})
    assert loss0 == (0, len(A) - (p - 1), 0)

    tests = ((F(0), True), (gam, True), (F(2), True), (F(2), False))
    for lam, live in tests:
        A1, b1 = append(A, b, p, lam, live)
        e1 = [F(1)] * len(A1)
        c1 = apply(A1, e1)
        q = tuple(2*ac - cc*cc for ac, cc in zip(apply(A1, c1), c1))
        assert not any(q[:len(A)]) and all(q[len(A):])
        assert len(set(c1[len(A):])) == len(A1) - len(A)
        assert not (set(c1[len(A):]) & set(c1[:len(A)]))
        assert apply(A1, q) == tuple(lam*q_i for q_i in q)
        assert dot(b1, q) == 0
        if live:
            assert dot(b1, [ci**(p-2)*qi for ci, qi in zip(c1, q)]) == -1
            if p >= 5:
                assert dot(b1, [qi*qi for qi in q]) == 0
        total += exact_full_order(A1, b1, p)

        physical, loss = ledger(A1, b1, e1, {gam})
        D, N, P, Q, labels = physical
        assert (P, Q) == (P0, Q0) and p == len(P) - 1 + 1
        assert p + sum(loss) == len(A1) + len(labels)
        assert p + sum(loss) + 1 > len(A1) + len(labels)

        B, beta, ee = quotient_by_line(A1, b1, q)
        quot, lossq = ledger(B, beta, ee, {gam})
        Dq, Nq, Pq, Qq, labelsq = quot
        assert (Pq, Qq) == (P, Q)
        G = trim((F(1), -lam))
        assert D == mul(G, Dq) and N == mul(G, Nq)
        L = len(labels - labelsq)
        assert L == (not live)
        assert loss == (lossq[0] + (lam != 0), lossq[1] + (lam == 0), lossq[2] + L)
        assert p + 1 + L + sum(lossq) == len(A1) + len(labels)
    return total


def main():
    # Counts include one baseline and four extensions (three all-live fans and a dead row).
    known = (1, 1, 2, 4, 9, 20, 48, 115)
    assert tuple(len(trees(n)) for n in range(1, 9)) == known
    checks = sum(check(p) for p in range(3, 9))
    assert checks == 5 * sum(sum(known[:p]) for p in range(3, 9))
    print(f"paid literal rooted-tree conditions: {checks} (orders 3 through 8)")
    print("verified 30 exact next tall failures; all 30 tall ledgers tight")
    print("verified 24 actual quotient ledgers: zero, retained, and fully lost pole cases")
    print("verified 18 live affine fan clock detectors; 12 paid isotropic fan cases")
    print("verified all 24 double-charge violations and 6 full-primary-block deletion charges")


if __name__ == '__main__':
    main()
