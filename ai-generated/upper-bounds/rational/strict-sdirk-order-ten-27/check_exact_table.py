#!/usr/bin/env python3
"""Exact arithmetic proof replay of the 27-stage rational SDIRK witness."""

from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import factorial
from pathlib import Path
import json


STAGES, ORDER, PASSIVE = 27, 10, 11
TABLE_SHA = "eb0075a13713d9bfb4249391d7d951693c172426ed891b924b2b5c81c0692081"
COUNTS = (1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862)
TALL = Fraction(5946972394780345710421384301593,
                224017752875470299449731184306688000000)


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def read_table():
    raw = Path(__file__).with_name("tableau.json").read_bytes()
    require(sha256(raw).hexdigest() == TABLE_SHA, "tableau.json fingerprint differs")
    data = json.loads(raw)
    require((data["stages"], data["order"], data["passive_core_rows"])
            == (STAGES, ORDER, PASSIVE), "wrong fixture dimensions")
    require(data["gamma"] == {"num": 1, "den": 9}, "wrong diagonal metadata")
    tall = data["next_tall_weight"]
    require(Fraction(tall["num"], tall["den"]) == TALL, "wrong tall metadata")
    return (data["a_integer"], data["b_integer"],
            data["a_denominator"], data["b_denominator"])


def replay(matrix, weights, d, e):
    require(len(matrix) == len(weights) == STAGES
            and all(len(row) == STAGES for row in matrix), "wrong tableau size")
    require(type(d) is int and type(e) is int and d > 0 and e > 0,
            "invalid integer scales")
    require(all(type(x) is int for row in matrix for x in row)
            and all(type(x) is int for x in weights), "noninteger numerator")
    require(all(9 * row[i] == d and not any(row[i + 1:])
                for i, row in enumerate(matrix)),
            "not lower triangular with common nonzero diagonal 1/9")
    require(weights[:PASSIVE] == [0] * PASSIVE
            and all(x > 0 for x in weights[PASSIVE:]), "wrong weight support")

    rows = [tuple((i, x) for i, x in enumerate(row) if x) for row in matrix]
    output = tuple((i, x) for i, x in enumerate(weights) if x)

    def matvec(values):
        return tuple(sum(x * values[i] for i, x in row) for row in rows)

    def dot(values):
        return sum(x * values[i] for i, x in output)

    # None is leaf; (u, v) is the reviewed butcherProduct u v.
    @lru_cache(None)
    def stage(tree):
        if tree is None:
            return 1, 1, (1,) * STAGES
        u, v = tree
        n0, f0, left = stage(u)
        n1, f1, _ = stage(v)
        return n0 + n1, f0 * n1 * f1, tuple(
            a * b for a, b in zip(left, acted(v))
        )

    @lru_cache(None)
    def acted(tree):
        return matvec(stage(tree)[2])

    trees = {1: (None,)}
    checked = []
    for n, expected_count in enumerate(COUNTS, 1):
        if n > 1:
            trees[n] = tuple((u, v) for j in range(1, n)
                             for u in trees[j] for v in trees[n - j])
        current = trees[n]
        require(len(current) == len(set(current)) == expected_count,
                f"wrong or duplicate enumeration at order {n}")
        rhs = e * d ** (n - 1)
        for i, tree in enumerate(current):
            size, forest_factorial, phi = stage(tree)
            require(size == n and size * forest_factorial * dot(phi) == rhs,
                    f"failed rooted-tree identity: order {n}, tree {i}: {tree!r}")
        checked.append({"order": n, "rooted_tree_presentations": len(current)})

    count = sum(row["rooted_tree_presentations"] for row in checked)
    require(count == 6918, "wrong total rooted-tree coverage")
    tall = None
    for _ in range(ORDER):
        tall = (None, tall)
    size, forest_factorial, phi = stage(tall)
    tall_factorial = size * forest_factorial
    require(size == ORDER + 1 and tall_factorial == factorial(size),
            "unexpected factorial of the eleventh tall tree")
    actual = Fraction(dot(phi), e * d ** (size - 1))
    required = Fraction(1, tall_factorial)
    require(actual == TALL and actual != required, "missing exact tall obstruction")

    return {
        "verification": "exact integer and rational arithmetic; Lean certificate pending",
        "stages": STAGES,
        "common_diagonal": "1/9",
        "satisfied_through_order": ORDER,
        "failed_order": size,
        "rooted_tree_presentations_checked": count,
        "counts_by_order": checked,
        "eleventh_tall_weight": str(actual),
        "required_eleventh_tall_weight": str(required),
    }


if __name__ == "__main__":
    print(json.dumps(replay(*read_table()), indent=2))
