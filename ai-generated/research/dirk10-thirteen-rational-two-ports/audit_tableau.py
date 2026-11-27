"""Standard-library exact independent audit of the literal rational DIRK."""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import json

t = json.loads(Path(__file__).with_name("tableau.json").read_text())
s = t["stages"]
assert (s, t["order"]) == (13, 10)
A = [[Q(v) for v in r] for r in t["A"]]
b = list(map(Q, t["b"]))
assert len(A) == len(b) == s
assert [len(row) for row in A] == list(range(1, s + 1))
assert len({A[i][i] for i in range(s) if A[i][i]}) > 1
assert len({tuple(row + [0] * (s - len(row))) for row in A}) == s
c = list(map(Q, t["c"]))
assert list(map(sum, A)) == c
D = lcm(*(v.denominator for row in A for v in row), *(v.denominator for v in b))
assert D == 126767366286331069785024000
assert D == 2**9 * 3**7 * 5**3 * 7 * 11**3 * 17 * 19**2 * 23 * 29 * 41 * 653 * 887

# For a tree of size k the integer vector below is Phi_t(D*A).
# Each stored action is (D*A) Phi_t(D*A); attaching a child
# costs its complete child size. This does not assume the constructor's
# reflector, projections, scalar rule, or merges.
N = [tuple((j, int(D * a)) for j, a in enumerate(row) if a) for row in A]
w = tuple(int(D * v) for v in b)
def mul(M, u):
    return tuple(sum(a * u[j] for j, a in row) for row in M)
entries = []
counts = []
for order in range(1, 11):
    layer = []
    def children(total, start, vec, factorial):
        if total == 0:
            assert factorial * sum(wi * v for wi, v in zip(w, vec)) == D**order
            layer.append((order, factorial, mul(N, vec)))
        else:
            for j in range(start, len(entries)):
                n, f, act = entries[j]
                if n > total:
                    break
                children(total - n, j, tuple(a * d for a, d in zip(vec, act)), factorial * f)
    children(order - 1, 0, (1,) * s, order)
    counts.append(len(layer))
    entries.extend(layer)
assert counts == [1,1,2,4,9,20,48,115,286,719] and len(entries) == 1205

delta = sum(wi * xi**10 for wi, xi in zip(b, c)) - Q(1, 11)
assert delta == Q(t["eleventh_bush_defect"]) == Q(1, 27371520)
assert 11 * delta == Q(1, 2488320) and D**2 % 2488320 == 0
print("literal 13-stage lower triangular tableau, 13 distinct rows and unequal nonzero diagonals")
print("all", sum(counts), "integer rooted equations:", counts)
print("eleventh-bush raw defect:", delta, "; normalized defect:", 11*delta)
print("stage and weight denominator:", D, "; 2488320 divides D^2")
