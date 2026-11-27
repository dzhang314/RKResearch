#!/usr/bin/env python3
"""Exact replay and Lean fixture generation for Zenodo 15429897.

Uses only Python's standard library. The generated cache is untrusted and
its recurrence, output residuals, and all canonical joins are checked in Lean.
"""
from collections import Counter
from functools import reduce
from hashlib import sha256
from fractions import Fraction
from math import gcd, lcm, prod
from pathlib import Path
import argparse

DEFAULT_SOURCE = (Path(__file__).parent.parent /
                  "erk10-stepanov-five-opening" / "stepanov15-source.txt")
NS = "RKResearch.Certified.ERK10Stepanov"
MODULE = "RKCert.ReviewedNative."
SOURCE_SHA = "72b63e2ea2aaf3a4cf340e65d2ebc8f56e34accce5f36026543260c398ca869f"
ZERO = (0,) * 8
BUCKET = 32


def pack(a):
    return (a,) + (0,) * 7


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(a, b):
    return tuple(a * x for x in b)


def mul(a, b):
    out = [0] * 8
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            if not y:
                continue
            overlap = i & j
            v = x*y*(3 if overlap & 1 else 1)*(7 if overlap & 2 else 1)
            k = i ^ j
            if overlap & 4:
                out[k] += 147 * v
                out[k ^ 2] += (294 if k & 2 else 42) * v
            else:
                out[k] += v
    return tuple(out)


def dot(a, b):
    return reduce(add, (mul(x, y) for x, y in zip(a, b) if x != ZERO and y != ZERO), ZERO)


def read_method(source):
    data = source.read_bytes()
    assert sha256(data).hexdigest() == SOURCE_SHA
    raw = [list(map(int, line.split())) for line in data.splitlines()]
    assert len(raw) == 135 and all(len(row) == 9 and row[-1] > 0 for row in raw)

    def decode(row):
        a, b, c, d, e, f, g, h, q = row
        v = (63*a, 63*b, 63*c, 63*d, 3*e, -2*f+7*h, 3*g, f-2*h)
        return tuple(Fraction(x, 63*q) for x in v)

    normalized = list(map(decode, raw))
    D = lcm(*(x.denominator for row in normalized for x in row))
    rows = [tuple(int(x*D) for x in row) for row in normalized]
    c, b = rows[:15], rows[15:30]
    A = [rows[30+i*(i-1)//2:30+i*(i+1)//2] for i in range(15)]
    assert c == [reduce(add, row, ZERO) for row in A]
    return D, c, b, A


def catalogue(p):
    children, order, forest = [()], [1], [1]
    cutoff = [0, 1]
    for total in range(2, p+1):
        previous = len(children)

        def lists(left, j):
            if left == 0:
                yield ()
                return
            for k in range(j, previous):
                if order[k] > left:
                    break
                for rest in lists(left-order[k], k):
                    yield (k,) + rest

        for child in lists(total-1, 0):
            children.append(child)
            order.append(total)
            forest.append(prod(order[k]*forest[k] for k in child))
        cutoff.append(len(children))
    assert len(children) == len(set(children))
    ids = {row: i for i, row in enumerate(children)}
    joins = [
        [ids[tuple(sorted(row + (j,)))] for j in range(cutoff[p-k])]
        for row, k in zip(children[:cutoff[p-1]], order)
    ]
    return children, order, forest, cutoff, joins


def audit(D, c, b, A, children, order, forest):
    deriv, checked = [], Counter()
    for i, (ch, n, f) in enumerate(zip(children, order, forest)):
        stage = tuple(reduce(mul, (deriv[j][s] for j in ch), pack(1)) for s in range(15))
        rhs = pack(D**n)
        assert scale(n*f, dot(b, stage)) == rhs, (i, ch, n)
        checked[n] += 1
        if n < 10:
            deriv.append(tuple(dot(row, stage) for row in A))

    def pow_const(a, n):
        return reduce(mul, [a]*n, pack(1))

    bush_num = scale(11, dot(b, [pow_const(x, 10) for x in c]))
    assert bush_num[1:] == ZERO[1:]
    defect = Fraction(bush_num[0], D**11) - 1
    assert defect

    # Independent check of chronological tall recursion, should a bush
    # defect be killed by a positive-characteristic coefficient map.
    tall = (pack(1),)*15
    for _ in range(10):
        tall = tuple(dot(row, tall) for row in A)
    tall_num = scale(prod(range(1, 12)), dot(b, tall))
    tall_defect = tuple(Fraction(tall_num[k], D**11) - (k == 0) for k in range(8))
    print("Source SHA256:", SOURCE_SHA)
    print("Common denominator:", D)
    print("Conditions by order:", dict(checked), "; total:", sum(checked.values()))
    print("Eleventh bush normalized residual:", defect)
    print("Eleventh tall normalized residual coordinates:", tall_defect)
    return deriv, defect


def arr(items):
    return "#[" + ", ".join(items) + "]"


def pair(u):
    return "(" + ",".join(map(str, u)) + ")"


def fmt_c8(u):
    return "(" + ",".join(
        "(" + pair(u[i:i+2]) + "," + pair(u[i+2:i+4]) + ")"
        for i in (0, 4)
    ) + ")"


def fmt_atom(u, n, D):
    if u == ZERO:
        return "pack 0"
    g = gcd(D**n, *u)
    den = D**n // g
    atom = tuple(x//g for x in u)
    base = f"pack ({atom[0]})" if not any(atom[1:]) else fmt_c8(atom)
    return f"expand {n} {den} ({base})"


def write(emit, name, imports, body, extra=""):
    header = ("module\n\n" + "\n".join("public import " + x for x in imports) +
              extra + "\n\n@[expose] public section\n\n"
              "/-! Generated by research/erk10-stepanov-native-upper/generate.py. -/\n\n"
              "namespace " + NS + "\n\n"
              "open ERKNestedRadicalReplay CanonicalStageMemo\n\n"
              "set_option maxRecDepth 30000\nset_option maxHeartbeats 0\n\n")
    (emit / (name + ".lean")).write_text(header + body + "\n\nend " + NS + "\n")


def blocks(rows, n=BUCKET):
    return [rows[i:i+n] for i in range(0, len(rows), n)]


def emit_fixture(emit, D, c, b, A, ch, order, forest, cut, joins, deriv, defect):
    p = "def D : ℤ := " + str(D) + "\n"
    p += """
def scale2 (g : ℤ) (u : ERKQuadraticIntegerReplay.Pair) :=
  (g*u.1, g*u.2)
def scale4 (g : ℤ) (u : C4) : C4 :=
  (scale2 g u.1, scale2 g u.2)
def content (g : ℤ) (u : C8) : C8 :=
  (scale4 g u.1, scale4 g u.2)
def expand (n : ℕ) (den : ℤ) (u : C8) := content (D^n / den) u
"""
    fmt = lambda z: fmt_atom(z, 1, D)
    p += "def clockNums : Array C8 := " + arr(map(fmt, c)) + "\n"
    p += "def bNums : Array C8 := " + arr(map(fmt, b)) + "\n"
    p += "def aNums : Array (Array C8) := #[\n  " + ",\n  ".join(
        arr(map(fmt, a)) for a in A) + " ]\n"
    p += """
def Cnum (i : Fin 15) : C8 := clockNums[i.val]!
def Bnum (i : Fin 15) : C8 := bNums[i.val]!
def Anum (i j : Fin 15) : C8 := if j < i then (aNums[i.val]!)[j.val]! else pack 0
"""
    p += f"def bushMult : ℤ := {defect.denominator}\n"
    p += f"def bushResid : ℤ := {defect.numerator}\n"
    p += f"\nabbrev Count := {len(ch)}\n"
    p += f"abbrev DerivCount := {len(deriv)}\n"
    p += """
def tag (i : ℕ) : Fin Count := ⟨i % Count, Nat.mod_lt _ (by decide)⟩
def leafId : Fin Count := tag 0
abbrev PackedKey := ℕ × ℕ × List ℕ
def unpackKey (k : PackedKey) : Key Count := ⟨k.1, k.2.1, k.2.2.map tag⟩
"""
    p += f"\ndef cutoff (n : ℕ) : ℕ := ({arr(map(str, cut))} : Array ℕ)[n]!\n"
    p += f"\ndef width : ℕ := {BUCKET}\n"
    write(emit, "ERK10StepanovLiterals",
          [MODULE + "ERKNestedRadicalReplay", MODULE + "CanonicalStageMemo"], p)

    def bucket_fun(name, data, elem, fmt):
        rows = [f"  | {i} => #[\n    " +
                ",\n    ".join(map(fmt, row)) + " ]" for i, row in enumerate(blocks(data))]
        return f"def {name} : ℕ → Array {elem}\n" + "\n".join(rows) + "\n  | _ => #[]\n"

    join_body = bucket_fun("keyBucket", list(zip(order, forest, ch)), "PackedKey",
                           lambda r: f"({r[0]}, {r[1]}, {list(r[2])})")
    join_body += bucket_fun("joinBucket", joins, "(Array ℕ)", lambda row: arr(map(str, row)))
    join_body += """
def keys (i : Fin Count) : Key Count :=
  unpackKey ((keyBucket (i.val / width))[i.val % width]!)
def join (i j : Fin Count) : Fin Count :=
  tag (((joinBucket (i.val / width))[i.val % width]!)[j.val]!)
"""
    write(emit, "ERK10StepanovKeys", [MODULE + "ERK10StepanovLiterals"], join_body)

    bucket_imports = []
    for k, rows in enumerate(blocks(list(zip(deriv, order)), 128)):
        name = "ERK10StepanovDeriv" + str(k)
        body = bucket_fun("derivBucket" + str(k), rows, "(Array C8)",
                          lambda pair: arr(fmt_atom(x, pair[1], D) for x in pair[0]))
        write(emit, name, [MODULE + "ERK10StepanovLiterals"], body)
        bucket_imports.append(MODULE + name)
    body = "def derivBucket (q : ℕ) : Array (Array C8) :=\n"
    body += "\n".join(
        f"  {'if' if k == 0 else 'else if'} q < {4*(k+1)} then "
        f"derivBucket{k} (q - {4*k})" for k in range(len(bucket_imports))) + "\n  else #[]\n"
    body += """
def deriv (i : Fin Count) (s : Fin 15) : C8 :=
  (((derivBucket (i.val / width))[i.val % width]!)[s.val]!)
"""
    write(emit, "ERK10StepanovDerivatives", bucket_imports, body)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    ap.add_argument("--emit", type=Path)
    args = ap.parse_args()
    D, c, b, A = read_method(args.source)
    ch, order, forest, cut, joins = catalogue(10)
    deriv, defect = audit(D, c, b, A, ch, order, forest)
    if args.emit:
        args.emit.mkdir(parents=True, exist_ok=True)
        emit_fixture(args.emit, D, c, b, A, ch, order, forest, cut, joins, deriv, defect)


if __name__ == "__main__":
    main()
