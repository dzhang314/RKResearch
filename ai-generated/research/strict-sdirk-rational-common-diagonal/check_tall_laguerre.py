#!/usr/bin/env python3
"""Exhaust the signed rational-root candidates for F_s, 2 <= s <= 19."""

from collections import Counter
from fractions import Fraction
from math import comb, factorial, prod


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sign(k):
    return -1 if k % 2 else 1


def moment_coefficients(s):
    # Ascending coefficients of x^s (s+1)! S_s(1/x).
    return tuple(
        sign(s - j) * comb(s, j) * prod(range(j + 2, s + 2))
        for j in range(s + 1)
    )


def laguerre_coefficients(s):
    # Ascending coefficients of (-1)^s s! L_s^(1)(x).
    return tuple(
        sign(s + j) * comb(s + 1, s - j) * prod(range(j + 1, s + 1))
        for j in range(s + 1)
    )


def factor_small(n):
    # First available divisor is prime after all smaller ones were removed.
    prime_powers = Counter()
    q = 2
    while q * q <= n:
        while n % q == 0:
            prime_powers[q] += 1
            n //= q
        q += 1
    if n > 1:
        prime_powers[n] += 1
    return prime_powers


def positive_divisors_of_factorial(n):
    powers = Counter()
    for k in range(2, n + 1):
        powers.update(factor_small(k))
    value = factorial(n)
    require(prod(q ** e for q, e in powers.items()) == value, (n, "factorial"))
    divisors = [1]
    for q, e in sorted(powers.items()):
        divisors = [d * q ** j for d in divisors for j in range(e + 1)]
    require(len(divisors) == prod(e + 1 for e in powers.values()), (n, "count"))
    require(len(set(divisors)) == len(divisors), (n, "duplicate divisor"))
    require(all(d > 0 and value % d == 0 for d in divisors), (n, "not divisors"))
    return divisors


def horner(c, x):
    value = 0
    for a in reversed(c):
        value = value * x + a
    return value


def tall_moment_polynomial(s, g):
    return sum(
        comb(s, j) * (-g) ** (s - j) / factorial(j + 1)
        for j in range(s + 1)
    )


def main():
    require(moment_coefficients(1) == laguerre_coefficients(1) == (-2, 1),
            "one-stage boundary polynomial")
    require(tall_moment_polynomial(1, Fraction(1, 2)) == 0,
            "one-stage order-two boundary")
    print(" s  threshold p  signed candidates  rational roots")
    total = 0
    for s in range(2, 20):
        c = moment_coefficients(s)
        require(c == laguerre_coefficients(s), (s, "different normalizations"))
        require(c[-1] == 1 and c[0] == sign(s) * factorial(s + 1),
                (s, "monic/end coefficients"))
        require(tall_moment_polynomial(s, Fraction(0)) == Fraction(1, factorial(s + 1)),
                (s, "zero common diagonal"))
        for g in (Fraction(1, 6), Fraction(-3, 5), Fraction(4, 3)):
            left = factorial(s + 1) * tall_moment_polynomial(s, g)
            require(left == g ** s * horner(c, 1 / g), (s, g, "reciprocal identity"))
        roots = []
        checked = 0
        for d in positive_divisors_of_factorial(s + 1):
            for x in (d, -d):
                checked += 1
                if horner(c, x) == 0:
                    roots.append(x)
        require(not roots, (s, "rational roots", roots))
        print(f"{s:2} {s+1:12} {checked:18} {len(roots):15}")
        total += checked
    print(f"PASS: widths 2..19, {total} signed candidates, no rational roots.")


if __name__ == "__main__":
    main()
