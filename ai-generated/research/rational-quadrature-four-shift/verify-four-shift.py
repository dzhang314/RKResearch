#!/usr/bin/env python3
"""Exact arithmetic for the finite part of the four-shift support proof."""
from collections import Counter
from math import comb, lcm


def check(test, label):
    if not test:
        raise AssertionError(label)


L = lcm(*range(1, 21))
check(L == 232792560, "clearing denominator")
mask = {d: (7 * (L // d)) % 8 for d in range(1, 21)}
check({d: v for d, v in mask.items() if v} ==
      {4: 4, 8: 2, 12: 4, 16: 1, 20: 4}, "mod-8 multipliers")
print("Cleared mod-8 multipliers:", [(d, v) for d, v in mask.items() if v])


def bit(t, u, k):
    return comb(t-u, k-u) % 2 if u <= k <= t else 0


def budget(t, u, k):
    return max(0, u-k, k-t)


def parity_tests(t, u):
    for j in range(4):
        if bit(t, u, 15-j):
            return False
        if budget(t, u, 15-j) >= 2 and bit(t, u, 7-j):
            return False
    return True


orientations = [(t, u) for t in range(17) for u in range(t+1) if 2*u >= t]
check(len(orientations) == 81, "oriented count")
survivors = [(t, u) for t, u in orientations if parity_tests(t, u)]
expected = {0: [0], 1: [1], 2: [1, 2], 3: [2, 3], 8: [8], 9: [8, 9],
            10: [8, 9, 10], 11: [8, 9, 10, 11], 16: [8, 16]}
check(survivors == [(t, u) for t, us in expected.items() for u in us],
      "complete oriented parity classification")
check(len(survivors) == 18, "survivor count")
print("Oriented count pairs: 81; parity survivors:", survivors)

payoffs = []
for t, u in survivors:
    if (t, u) == (16, 8):
        continue
    if t <= 3:
        j, k = 3-t, t
    elif (t, u) == (11, 8):
        j, k = 1, 10
    elif (t, u) == (16, 16):
        j, k = 3, 16
    else:
        j, k = 11-t, t
    check(0 <= j < 4 and 0 <= k <= 16, ("row scope", t, u))
    check(mask[k+j+1] == 4 and bit(t, u, k) == 1, ("live term", t, u))
    # k <= 16 includes all potentially nonzero coefficients of P.
    for i in range(17):
        if i != k:
            check(mask[i+j+1] * 2**budget(t, u, i) % 8 == 0,
                  ("vanishing term", t, u, j, i))
    payoffs.append((t, u, j, k))
check(len(payoffs) == 17, "one-term exclusion count")
print("One-term obstructions (t, u, shift, index):", payoffs)


def monic_product_mod4(roots):
    coeffs = [1]
    for r in roots:
        out = [0] * (len(coeffs)+1)
        for i, a in enumerate(coeffs):
            out[i] = (out[i]-r*a) % 4
            out[i+1] = (out[i+1]+a) % 4
        coeffs = out
    return coeffs


pairs = Counter()
for e in range(9):
    for o in range(9):
        p = monic_product_mod4([0]*(8-e) + [2]*e + [1]*(8-o) + [3]*o)
        check((p[12]-p[14]) % 4 == 2, ("balanced gap", e, o))
        pairs[p[12], p[14]] += 1
check(pairs == {(0, 2): 36, (2, 0): 45}, "balanced classification")
print("Balanced (a12, a14) counts across 81 multisets:",
      sorted(pairs.items()))
print("PASS: all exact finite steps; no tableaux, numerical search, or Lean.")
