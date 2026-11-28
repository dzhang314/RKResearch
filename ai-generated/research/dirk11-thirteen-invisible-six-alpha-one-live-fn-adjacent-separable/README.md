# The adjacent carrier quadratic is separable in the live direct Fn chart

**Result.** In the remaining normalized no-late invisible-six
DIRK11/13 chart with live reciprocal multiplier, \(\alpha=\beta=1\),
direct noncontact \(F_n\), and nonzero fourth and fifth regular
reverse diagonals, the actual adjacent equation in carrier \(E=qK_*\)
has nonzero discriminant. Together with the
[live quadratic leader](../dirk11-thirteen-invisible-six-alpha-one-live-fn-adjacent-quadratic/README.md),
it is a genuinely separable monic quadratic at every candidate.
This is not an exclusion of the generic beta-one chart or a
stage-count improvement.

Use the actual carrier \(A(E)=a_0+a_1E+a_2E^2\) from the
[fifth-compensator packet](../dirk11-thirteen-invisible-six-alpha-one-live-fn-fifth-compensator/README.md),
built from the true \(Q_4\) primitive coefficient at \(Y\)
and the compensated old fits. The exact leader proof gives
\(a_2\ne0\). If \(\Delta_A=a_1^2-4a_0a_2=0\), the identity
\[
 (2a_2E+a_1)^2=4a_2 A(E)+\Delta_A
\]
forces \(E=-a_1/(2a_2)\) at an actual characteristic-zero
field candidate. No numerical radical choice, clock
ordering or assumption on repeated roots elsewhere in
the model is necessary.

## Exact finite projection of the repeated-root slice

Use the scaled monic rank-12 ordinary and direct \(F_n\)
clock algebra over \(\mathbb Q[V]\) from the linked
fifth-compensator proof. **project.py** computes the exact
norm of the discriminant, with only the known ordinary
forbidden content removed. The absolute norm has raw
degree **2808**, squarefree degree **260**.
Beyond \(J_4,E_+\), its complete irreducible support is:

| Factor | Live guard | Exact cap | Residue degree at 103 |
|---|---|---:|---:|
| degree 12, constant 16227 | homogeneous \(c_1+6s\) | 11 | 12 |
| degree 12, constant 54123 | \(c_2\) in lower rank-four algebra | 9 | 4 |
| degree 48, constant 1865429207937 | homogeneous first-gap \(q\) | 11 | 1 |
| degree 60, constant −1461941766456 | old \(m\)-multiplication determinant | 11 | 1 |
| degree 120, constant 1224003691778934976981908885504 | 1 | 12 | 1 |

On each nontrivial guard the exact factor divides the
corresponding guard norm, checked in **project.py**.
The cap-nine case uses the norm in the lower rank-four
ordinary algebra and its free cubic extension.
Each guard is live at an actual candidate.

The other used scalar is the true first-middle commutator
after the exact \(d_x=0\) and live affine \(x\) pin,
with its homogeneous carrier-degree-four numerator
from the adjacent quadratic leader proof.
Evaluate that numerator homogeneously at
\((-a_1,2a_2)\), keeping the fixed degree bound four.
The coefficient leading \(a_2\) is live at actual points,
and no specialized degree assumption is used for
this first-middle numerator.

**rank.py** checks the summed multiplication images
of the guard times the pure discriminant and the guard
times this pinned first-middle numerator. At 103 the
ranks are **132, 36, 11, 11, 12**, matching the exact caps
times the residue degrees; in the new degree-120 case
the chosen residue is \(V+15\).
The exact characteristic-zero image therefore contains
the full guard image. Evaluation at a candidate killing
both actual gates would kill its live guard, a contradiction.
No unknown clock, tableau coefficient or carrier has
been reduced modulo any prime.

**Replay.** Run **bash verify.sh** with SymPy and
python-flint 0.9. The independent rational-coordinate
check verifies the adjacent scale and completed-square
identity on four exact probes. The rank argument is
a reproducible exact source proof, not an end-to-end
Lean tableau theorem.
