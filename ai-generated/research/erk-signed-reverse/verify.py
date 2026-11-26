"""Verify signed-reverse tableaux using exact integers; exhaustive through order 14."""

from argparse import ArgumentParser
import json
from fractions import Fraction
from functools import cache
from math import gcd, lcm, prod
from pathlib import Path


parser=ArgumentParser(description=__doc__)
parser.add_argument("p", type=int, choices=range(11,21))
parser.add_argument("--all", action="store_true", help="exhaustive replay (through order 14)")
args=parser.parse_args()
p=args.p
assert not args.all or p<=14

def paid_remainder(n):
    n = abs(n)
    for prime in (2, 3, 5, 7, 11, 13, 17, 19):
        if prime > p:
            continue
        while n and n % prime == 0:
            n //= prime
    return n


data = json.loads(Path(__file__).with_name(f"tableau-{p}.json").read_text())
A = [tuple(map(Fraction, row)) for row in data["A"]]
b = tuple(map(Fraction, data["b"]))
s = (25,28,33,37,44,50,57,63,71,79)[p-11]
assert len(A) == len(b) == s
assert all(len(row) >= i and not any(row[i:]) for i, row in enumerate(A))
assert len({row[:i] + (0,) * (s - i) for i, row in enumerate(A)}) == s
D = lcm(*(v.denominator for row in A for v in row), *(v.denominator for v in b))
assert paid_remainder(D) == 1

# Scaling A by D scales the weight vector of a size-n tree by D**(n-1).
scaled_A = [
    tuple((j, int(D * value)) for j, value in enumerate(row) if value)
    for row in A
]
scaled_b = tuple(int(D * value) for value in b)


@cache
def forests(n, lower=(0, ())):
    if n == 0:
        return ((),)
    return tuple(
        (branch,) + tail
        for k in range(max(1, lower[0]), n + 1)
        for branch in trees(k)
        if (k, branch) >= lower
        for tail in forests(n - k, (k, branch))
    )


@cache
def trees(n):
    return forests(n - 1)


@cache
def size(t):
    return 1 + sum(map(size, t))


@cache
def factorial(t):
    return size(t) * prod(map(factorial, t))


@cache
def weighted(t):
    branches = tuple(extension(child) for child in t)
    return tuple(prod(branch[i] for branch in branches) for i in range(s))


@cache
def extension(t):
    v = weighted(t)
    return tuple(sum(a * v[j] for j, a in row) for row in scaled_A)


def defect_numerator(t):
    return factorial(t) * sum(a * v for a, v in zip(scaled_b, weighted(t))) - D**size(t)



counts=(1,1,2,4,9,20,48,115,286,719,1842,4766,12486,32973)
if args.all:
    test_count=0
    for n in range(1,p+1):
        ts=trees(n)
        assert len(ts)==counts[n-1]
        assert all(defect_numerator(t)==0 for t in ts),n
        test_count+=len(ts)
    print(f"order {p}, {s} stages: all {test_count} rooted conditions")
else:
    tested={t for n in range(1,9) for t in trees(n)}
    for n in range(9,p+1):
        for k in range(1,n):
            t=((),)*(k-1)
            while size(t)<n:
                t=(t,)
            tested.add(t)
            tested.add((((),)*(k-1),)+((),)*(n-k-1))
    assert all(defect_numerator(t)==0 for t in tested)
    print(f"order {p}, {s} stages: {len(tested)} sampled rooted conditions")
def tuple_tree(t):
    return tuple(tuple_tree(branch) for branch in t)


raw_witnesses = json.loads(Path(__file__).with_name(f"witness-{p}.json").read_text())
running = 0
for raw_tree, raw_value in raw_witnesses:
    t = tuple_tree(raw_tree)
    assert size(t) == p+1
    val = Fraction(defect_numerator(t), D**(p+1))
    assert val == Fraction(raw_value)
    assert paid_remainder(val.denominator) == 1
    running = gcd(running, paid_remainder(val.numerator))
assert running == 1
print(f"{len(raw_witnesses)} next-order defects generate the unit ideal")
