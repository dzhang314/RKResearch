# Lean certificate for the rational fifteen-stage ERK9 witness

The earlier [exact tableau and independent integer replay](../erk9-fifteen-rational-moment-splice/README.md)
now also have closed Lean theorems on the reviewed literal order predicate.
The source preserves exactly the same rational coefficients, with the
common denominator \(D\) printed in the underlying data and replay.

- **RKResearch.Certified.ERK9RationalFifteen.order_nine** proves the
  reviewed HasOrder 9 for the literal matrix and weights over any
  commutative ring in which \(D\) admits its inverse.
- **.exists_exact_of_unit** combines strictness and exact order nine
  over every nontrivial commutative ring paying this \(D\).
- **.exists_exact_charZero** and **.exists_exact_rational** give the
  same fifteen physical stages over any characteristic-zero field
  and over the rationals, respectively.

The literal identities are checked with a compressed cache of 327
normalized profiles and 145 integer actions. Its 616 compatible
joins, leaf coverage and all output moments are checked, and
structural induction covers every presentation of a reviewed tree.
The denominator restoration is reviewed scalar homogeneity.
The tenth bush has cleared residual 5 after multiplication by 9984.
Since 5 divides \(D\), it is a unit in any specialization considered
here, providing the next-order failure without positivity.

From ai-generated/lean, with matching Mathlib:

    lake build +RKCert.ReviewedNative.ERK9RationalFifteen

To regenerate the untrusted fixture inputs, point generate_lean.py
at the original JSON in the sibling research directory and supply
the ReviewedNative directory with --emit and a scratch list path
with --modules. The Python generator is not a theorem premise.

The accompanying audit is on Lean 4.36.0 with its pinned Mathlib;
all endpoints report only the standard axioms propext,
Classical.choice and Quot.sound. The full dependency graph was not
rerun on other Lean versions. The uniform arbitrary-ring,
factorial-localized upper bound of sixteen is not replaced by this
literal fifteen-stage denominator.
