# Native integer structural certificate of the universal DIRK12 width twenty

The end-to-end theorem is
\(\texttt{RKResearch.Certified.DIRK12FactorialTwentyFlag.exists\_exact\_factorial}\).
It gives a literal lower triangular twenty-stage tableau over every
nonzero commutative ring with \(12!\) a unit. It has \(A_{00}=0\),
\(16 A_{11}=1\), reviewed rooted order twelve, and fails order
thirteen. The separate stronger nineteen-stage bound over local,
clean, and finite-characteristic coefficient rings is not inferred
from this theorem.

The [literal arithmetic JSON](tableau20.json) is unchanged.
Generate the integer flag data in a temporary source directory:

    python3 -B generate-integer-flags.py tableau20.json /path/to/temporary/source

Then compare the generated DIRK12FactorialTwentyFlagData.lean
byte-for-byte to the committed source. The other modules contain
proofs and closed receipts, not data from an external oracle.
Use ordinary Mathlib-pinned project imports and build in this order:

1. ScaledIntegerFlagReplay
2. DIRK12FactorialTwentyFlagData
3. DIRK12FactorialTwentyFlagChecks
4. DIRK12FactorialTwentyFlagActionsEarly
5. DIRK12FactorialTwentyFlagActionsLate
6. DIRK12FactorialTwentyFlagProducts
7. DIRK12FactorialTwentyFlag

## Structural certificate rather than a collection of trees

Take integer numerators \(M,\mathbf w\) using the ordinary common
scale \(D\). At each grade \(k\), the supplied integer direction
vectors define a subspace over \(\mathbb Q\). To check membership of
an integer input vector, the kernel verifies one scaled projection
equality of the form
\[
 L_k\mathbf v=\sum_j v_{p_j} a_{kj}\,\mathbf z_{kj},
 \qquad L_k\ne0.
\]
A proof over \(\mathbb Q\) turns that particular equality into
membership in the span. Independence and completeness of the
supplied basis, or the correctness of the Python row reduction,
are not assumptions. The numeric evaluator never divides by the
rational pivot coordinates.

The tested physical grades have ranks
\(0,0,0,1,2,4,6,10,14,16,17,18\) through grade eleven. The
integer receipts check their stage and clock actions, products,
primitive discrepancies, and silent weighted outputs. They
also check the twelve scaled scalar equations. The generic
bridge supplies the usual sufficient rooted flags, proves
every rational order condition, and recovers the cleared
integer equations by injectivity. The reviewed scaled-moment
theorem then transfers those integer equations to the target
ring using only the actual literal normalization. No extra
flag pivot is required to be a unit there.

## Short exact-order test

The independent arithmetic receipt uses the tall tree as a
second unpaid test. The kernel proof uses a smaller exact
companion: the order-thirteen tree whose root has three leaf
children and one nine-vertex bush child. It has factorial 117
and elementary vector
\(\mathbf c^3\odot A\mathbf c^8\).
For the two normalized defects, the verified integer equations
clear the actual tableau denominator and give
\[
  \delta_{\mathrm{bush}}=\frac{97351}{161663040},\qquad
  \delta_{\mathrm{mixed}}=-\frac{281923}{95800320}.
\]
The integer relation
\(1642(97351)+567(-281923)=1\) rules out both paid conditions
at order thirteen after every coefficient specialization.
The proof only cancels powers of the actual scale \(D\), a
unit because \(D\mid(12!)^6\).

The direct proof and axiom audit use pinned Lean/Mathlib 4.36.0.
All arithmetic decisions are checked by the Lean kernel. A
full replay with matching Mathlib dependencies on other Lean
versions is a separate compatibility check.

The literal compile closure and an independent, typed final
import are listed in [native-modules.txt](native-modules.txt)
and [native-audit.lean](native-audit.lean). In the integrated
checkout, the graded replay recipe is:

    bash replay-native.sh

The attached transcript records the pinned release, exact
generation ranks, endpoint declarations and typed audit. This
new certificate is a matched Mathlib proof, not a standalone
multi-release Lean-core sentinel.
