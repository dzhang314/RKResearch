#!/usr/bin/env python3
"""Independent standard-library DIRK11 finite-field and Hensel replay."""
from fractions import Fraction
from functools import cache
from hashlib import sha256
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
TABLEAU = HERE.parent / "dirk11-width14-real-reflected-shell" / "tableau.json"
TABLEAU_SHA = "4a59259a370bf206246961345e06dd158a12b82c82872880eaa7e725e20d7b00"
assert sha256(TABLEAU.read_bytes()).hexdigest() == TABLEAU_SHA
DATA = json.loads(TABLEAU.read_bytes())
SEEDS = json.loads((HERE / "seeds.json").read_bytes())
KEYS = ("relations", "A", "b", "scaled_failure")

def denominators(data):
    if isinstance(data, list):
        return lcm(*(denominators(x) for x in data))
    return Fraction(data).denominator

D0 = lcm(*(denominators(DATA[key]) for key in KEYS))
D = lcm(D0, denominators(DATA["scaled_failure_inverse"]))
assert D == 11802927079442476328220631032515414837531751717282029889926774726222015333151773368050816000

@cache
def scalar(value, modulus):
    value = Fraction(value)
    return value.numerator * pow(value.denominator, -1, modulus) % modulus

def specialize(block, roots, modulus):
    if not roots:
        assert isinstance(block, str)
        return scalar(block, modulus)
    assert len(block) == 2
    lo, hi = (specialize(x, roots[:-1], modulus) for x in block)
    return (lo + roots[-1] * hi) % modulus

def relation(i, roots, modulus):
    a, b, c = (specialize(coef, roots, modulus) for coef in DATA["relations"][i])
    assert b == 0 or i == 3
    assert c == 1
    return a, b

def check_roots(roots, prime, modulus):
    derivatives = []
    for i, root in enumerate(roots):
        a, b = relation(i, roots[:i], modulus)
        assert (root * (root + b) + a) % modulus == 0
        derivative = (2 * root + b) % prime
        assert derivative
        derivatives.append(derivative)
    return derivatives

def lift(roots, prime, exponent):
    roots = list(roots)
    base = prime
    for _ in range(1, exponent):
        modulus = base * prime
        for i, root in enumerate(roots):
            a, b = relation(i, roots[:i], modulus)
            value = (root * (root + b) + a) % modulus
            assert value % base == 0
            correction = -(value // base) * pow(2 * root + b, -1, prime) % prime
            roots[i] = root + base * correction
        base = modulus
    return roots

def dot(weights, values, modulus):
    return sum(x*y for x, y in zip(weights, values)) % modulus

def full_replay(roots, prime, modulus):
    assert gcd(D0, modulus) == 1
    derivatives = check_roots(roots, prime, modulus)
    A = [[specialize(x, roots, modulus) for x in row] for row in DATA["A"]]
    weights = [specialize(x, roots, modulus) for x in DATA["b"]]
    assert [len(row) for row in A] == list(range(1, 15))
    assert len(weights) == 14
    act = lambda v: tuple(dot(row, v, modulus) for row in A)
    ones = (1,) * 14
    clock = act(ones)
    assert dot(weights, ones, modulus) == 1
    sizes = [1]
    densities = [1]
    reads = [clock]
    counts = [1]
    for size in range(2, 12):
        end = len(sizes)
        def forests(rem, start):
            if rem == 0:
                yield ()
                return
            for j in range(start, end):
                if sizes[j] > rem:
                    break
                for rest in forests(rem-sizes[j], j):
                    yield (j,) + rest
        for children in forests(size-1, 0):
            stage = tuple(prod(reads[j][i] for j in children) % modulus for i in range(14))
            density = size * prod(densities[j] for j in children)
            assert density * dot(weights, stage, modulus) % modulus == 1, (modulus, size, children)
            sizes.append(size)
            densities.append(density)
            if size < 11:
                reads.append(act(stage))
        counts.append(len(sizes)-end)
    assert counts == [1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842]
    bush_child = act(tuple(pow(z, 6, modulus) for z in clock))
    defect = (84 * dot(weights, (pow(z, 4, modulus)*w for z, w in zip(clock, bush_child)), modulus)-1) % modulus
    assert defect == specialize(DATA["scaled_failure"], roots, modulus)
    assert gcd(defect, modulus) == 1
    if gcd(D, modulus) == 1:
        inv = specialize(DATA["scaled_failure_inverse"], roots, modulus)
        assert defect * inv % modulus == 1
    return A, weights, derivatives, defect

def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n)+1))

def main():
    assert len(SEEDS) == 68 and sorted(set(row[0] for row in SEEDS)) == [row[0] for row in SEEDS]
    print("tableau denominator", D0, flush=True)
    print("full denominator", D, flush=True)
    for p, *row in SEEDS:
        assert prime(p)
        roots, expected = row[:4], row[4]
        A, b, derivatives, defect = full_replay(roots, p, p)
        assert defect == expected
        for exponent in ((2, 3, 5) if p in (113, 709) else (2,)):
            lifted = lift(roots, p, exponent)
            mod = p ** exponent
            B, c, ders, ell = full_replay(lifted, p, mod)
            assert [[x % p for x in row] for row in B] == A
            assert [x % p for x in c] == b and ders == derivatives and ell % p == defect
            if p == 113 and exponent == 2:
                assert lifted == [4476, 2160, 1993, 4680] and ell == 382
            if p in (113, 709):
                print(f"p={p}, k={exponent}, roots={lifted}, defect={ell}", flush=True)
    assert gcd(D0, 709) == 1 and D % 709 == 0
    print("68 prime and prime-square tableaux plus four higher-power controls;",
          "all 3,047 rooted conditions and a unit next-order defect in each.", flush=True)

if __name__ == "__main__":
    main()
