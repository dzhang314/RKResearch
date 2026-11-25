#!/usr/bin/env python3
"""Check the published 27-stage strict rational SDIRK through order ten."""
from argparse import ArgumentParser
from collections import Counter
from contextlib import ExitStack
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import math
import sys

STAGES = 27
ORDER = 10
RANK = (0, 1, 1, 2, 4, 8, 12, 17, 24, 26)
PAIR_COUNT = (0, 0, 1, 2, 5, 12, 28, 56, 106, 194, 328)
TABLE_SHA = "eb0075a13713d9bfb4249391d7d951693c172426ed891b924b2b5c81c0692081"
COUNTS = {"basis": 95, "leaf": 1, "action": 95, "lower-pay": 95, "member": 404, "top-pay": 328}
STREAM_SHA = {
    "basis": "e38ce58404082cde938906ae13f7d1c19e7b282cf6819d263dddc1d4583ba610",
    "leaf": "3b87694107a25da24202c4bb3ac8b520b3111030967347435f15b9a78890ad37",
    "action": "9b74c4acd432ccb18a71459fbf87b12768a1380c4fc8bcd116520c2e5f177d88",
    "lower-pay": "a86edab65069f4478697417bbe8faf6d32dca93d57f8d3cc183c9f5f875e87d2",
    "member": "1243df977dcd271796cd179395eade58d253d90c47efffeec2b8a96ff8ffcc0c",
    "top-pay": "89b01039adbd05fb5ff0b55b43be99b3cb2dfa23a85a668cf2ac92ce9ebcd6bf",
}
PRODUCT_SHA = (
    "",
    "3a41153cf1666f14ff36889fad110c0c9c63a74288b9d99b9d43429ef88f0dbd",
    "ca49e018254aa524a948b8da584a04ba507fa5b8c6b8536cccffa9b5013090df",
    "7a833ab75a8433efe929bcecafb05dbdb2304f62a28ebf9f4f0193ec683d9c3f",
    "f81e25fc13ea0159519a3a551c7a899f30ea1b90131b8bee824487607f6d8c80",
    "fe88d05c2bbd508e058e03e138d18839a2bf93315698c47e7c7d0b50186dc076",
    "00536ead9d19781f9895913a496e3676038fda87f113eb7ab1033fd64b534592",
    "c27df622dc6ba7c07bdd53f89cd8a683e9b1133ea03b4b7b35e944b462863643",
    "dca2440ac63c40dce3a323332a0c1a514924660aff2526f7012c6b3f3eb62727",
    "3a273fd88aebc487145231179650562d4b6bb5bca4f1b395dd3c3b6239274b56",
    "11513bc8475b42d4f9733bc9de64d8cac5e5a81ea47337137efc6266251b515f",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def bits(value):
    return abs(value).bit_length()


def max_bits(values):
    return max(map(bits, values), default=0)


def decimals(values):
    return list(map(str, values))


def row_bytes(values):
    return (",".join(map(str, values)) + "\n").encode("ascii")


def exact_int(text):
    require(type(text) is str, "basis coordinates must be signed decimal strings")
    value = int(text)
    require(str(value) == text, "noncanonical decimal in basis")
    return value


def load_table(path):
    raw = path.read_bytes()
    require(sha256(raw).hexdigest() == TABLE_SHA, "tableau bytes differ from the published literal")
    table = json.loads(raw)
    matrix, weights = table["a_integer"], table["b_integer"]
    d, e = table["a_denominator"], table["b_denominator"]
    require(table["stages"] == STAGES and table["order"] == ORDER, "wrong tableau dimensions")
    require(len(matrix) == len(weights) == STAGES and all(len(row) == STAGES for row in matrix),
            "wrong matrix or output width")
    require(all(type(x) is int for row in matrix for x in row)
            and all(type(x) is int for x in [*weights, d, e]) and d > 0 and e > 0,
            "noninteger entries or invalid denominator")
    require(all(9 * row[i] == d and not any(row[i + 1:]) for i, row in enumerate(matrix)),
            "not a strict common-diagonal lower-triangular tableau")
    require(table["passive_core_rows"] == 11 and weights[:11] == [0] * 11
            and all(x > 0 for x in weights[11:]), "unexpected weights")
    return matrix, weights, d, e


def load_basis(path):
    raw = path.read_bytes()
    require(sha256(raw).hexdigest() == STREAM_SHA["basis"], "frozen basis bytes differ")
    records = raw.splitlines()
    require(len(records) == COUNTS["basis"], "wrong number of frozen basis rows")
    basis = {}
    at = 0
    for n in range(1, ORDER):
        rows = []
        for i in range(RANK[n]):
            record = json.loads(records[at])
            at += 1
            require(record["key"] == [n, i] and len(record["stage"]) == STAGES,
                    f"bad basis key or dimension {(n, i)}")
            row = tuple(map(exact_int, [*record["stage"], record["last"]]))
            require(row[i] > 0 and not any(row[:i]) and math.gcd(*row) == 1,
                    f"not a primitive echelon row {(n, i)}")
            rows.append(row)
        basis[n] = rows
    return basis


class Receipts:
    def __init__(self, stack, directory):
        self.hashes = {kind: sha256() for kind in COUNTS}
        self.counts = Counter()
        self.outputs = {}
        if directory is not None:
            directory.mkdir()  # Must be new; never overwrite an earlier receipt.
            for kind in COUNTS:
                self.outputs[kind] = stack.enter_context((directory / (kind + ".jsonl")).open("xb"))

    def record(self, kind, key, **fields):
        line = (json.dumps({"key": key, **fields}, sort_keys=True, separators=(",", ":")) + "\n")
        raw = line.encode("ascii")
        self.hashes[kind].update(raw)
        self.counts[kind] += 1
        if kind in self.outputs:
            require(self.outputs[kind].write(raw) == len(raw), f"incomplete write for {kind} {key}")

    def finalize(self):
        hashes = {kind: digest.hexdigest() for kind, digest in self.hashes.items()}
        require(self.counts == COUNTS, f"incomplete receipt coverage: {self.counts}")
        require(hashes == STREAM_SHA, "reproduced exact record streams differ")
        return hashes


def payment(n, row, weights, e, key):
    lhs = n * sum(w * x for w, x in zip(weights, row[:-1]))
    rhs = e * row[-1]
    require(lhs == rhs, f"payment at {key} failed")
    return {"scalar_left": str(lhs), "scalar_right": str(rhs), "scalar_bits": bits(lhs)}


def clearing(row, basis, key):
    # Echelon pivots determine unique coefficients; verify the full identity in Z.
    tail = list(map(Fraction, row))
    coefficients = []
    for i, source in enumerate(basis):
        coeff = tail[i] / source[i]
        coefficients.append(coeff)
        if coeff:
            for j in range(i, STAGES + 1):
                if source[j]:
                    tail[j] -= coeff * source[j]
    require(not any(tail), f"out of the certified rational span at {key}")
    denominator = math.lcm(*(c.denominator for c in coefficients))
    terms = [(i, c.numerator * (denominator // c.denominator))
             for i, c in enumerate(coefficients) if c]
    require(denominator > 0 and math.gcd(denominator, *(c for _, c in terms)) == 1,
            f"nonprimitive denominator clearing at {key}")
    lhs = tuple(denominator * z for z in row)
    sums = [0] * (STAGES + 1)
    term_bits = 0
    for i, c in terms:
        for j, z in enumerate(basis[i]):
            contribution = c * z
            sums[j] += contribution
            term_bits = max(term_bits, bits(contribution))
    require(tuple(sums) == lhs, f"integer clearing failed at {key}")
    return {
        "clearing": {"denominator": str(denominator), "terms": [[i, str(c)] for i, c in terms]},
        "cleared_decimal_sha256": sha256(row_bytes(lhs)).hexdigest(),
        "denominator_bits": bits(denominator),
        "coefficient_max_bits": max_bits(c for _, c in terms),
        "cleared_max_bits": max_bits(lhs),
        "individual_term_product_max_bits": term_bits,
    }


def action(matrix, branch_grade, stage):
    return tuple(branch_grade * sum(a * y for a, y in zip(row, stage)) for row in matrix)


def ordered_pairs(n):
    for k in range(1, n):
        ell = n - k
        for i in range(RANK[k]):
            for j in range(RANK[ell]):
                yield k, ell, i, j


def check(root, output):
    matrix, weights, d, e = load_table(root.parent / "tableau.json")
    basis = load_basis(root / "basis.jsonl")
    with ExitStack() as stack:
        receipts = Receipts(stack, output)
        cache = {}
        for n in range(1, ORDER):
            for i, row in enumerate(basis[n]):
                key = (n, i)
                receipts.record("basis", key, stage=decimals(row[:-1]), last=str(row[-1]),
                                feature_max_bits=max_bits(row))
                receipts.record("lower-pay", key, **payment(n, row, weights, e, key))
                act = action(matrix, n, row[:-1])
                receipts.record("action", key, stage=decimals(act), stage_max_bits=max_bits(act))
                cache[key] = act

        leaf = (1,) * (STAGES + 1)
        require(basis[1] == [leaf], "leaf is not the certified grade-one generator")
        require(sha256(row_bytes(leaf)).hexdigest() == PRODUCT_SHA[1], "wrong frozen leaf digest")
        receipts.record("leaf", (1,), joined_row=decimals(leaf),
                        clearing={"denominator": "1", "terms": [[0, "1"]]})

        for n in range(2, ORDER + 1):
            count = 0
            products = sha256()
            for k, ell, i, j in ordered_pairs(n):
                key = (n, k, ell, i, j)
                left, right = basis[k][i], basis[ell][j]
                stage = tuple(a * b for a, b in zip(left[:-1], cache[ell, j]))
                row = (*stage, d * left[-1] * right[-1])
                packed = row_bytes(row)
                products.update(packed)
                fields = {
                    "flat_index": count, "joined_row": decimals(row),
                    "joined_max_bits": max_bits(row), "joined_decimal_sha256": sha256(packed).hexdigest(),
                }
                if n < ORDER:
                    receipts.record("member", key, **fields, **clearing(row, basis[n], key))
                else:
                    receipts.record("top-pay", key, **fields, **payment(n, row, weights, e, key))
                count += 1
            require(count == PAIR_COUNT[n], f"wrong ordered pair count at order {n}")
            require(products.hexdigest() == PRODUCT_SHA[n], f"wrong ordered product digest at order {n}")
        hashes = receipts.finalize()
    return {
        "status": "PASS",
        "orders_checked": [1, ORDER],
        "basis_ranks_orders_1_to_9": list(RANK[1:]),
        "ordered_basis_products_per_order": list(PAIR_COUNT[1:]),
        "ordered_basis_products": sum(PAIR_COUNT),
        "receipt_counts": COUNTS,
        "canonical_jsonl_sha256": hashes,
        "next_tall_checked": False,
        "lean_checked": False,
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--emit-receipts", type=Path, metavar="NEW_DIRECTORY",
                        help="also write the six byte-reproducible JSONL streams")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(10000)  # The exact frozen integers are smaller.
    try:
        result = check(Path(__file__).resolve().parent, args.emit_receipts)
    except (KeyError, IndexError, OSError, TypeError, ValueError) as error:
        parser.exit(1, f"FAIL: {error}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
