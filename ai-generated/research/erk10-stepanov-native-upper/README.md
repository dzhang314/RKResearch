# Stepanov's 15-stage ERK10: an exact Lean certificate

This packet reconstructs the published 15-stage explicit order-ten
tableau, rather than assuming its parameterized order identities.
The coefficient source is the [authenticated Zenodo fixture](https://zenodo.org/records/15429897)
accompanying [Misha Stepanov's order-ten paper, §5](https://arxiv.org/html/2504.17329v2#S5).
The same bytes are stored in
[stepanov15-source.txt](../erk10-stepanov-five-opening/stepanov15-source.txt).
The local input SHA-256 is
72b63e2ea2aaf3a4cf340e65d2ebc8f56e34accce5f36026543260c398ca869f.

## Statements and coefficient domains

All statements refer to the literal reviewed `ERK` and `HasOrder`
predicates on a physical width-15 tableau. The bound is an upper bound,
not a claim of optimality at order ten.

- `RKResearch.Certified.ERK10Stepanov.order_ten` and
  `.not_order_eleven` certify the literal coefficient instance
  over a commutative ring. Exactness needs nontriviality. The common
  explicit integer \(D\) must be a unit and the coefficient ring must
  possess \(x,y,z\) with \(x^2=3,\ y^2=7,\ z^2=147+42y\).
- `.exact_with_roots` combines strictness, order ten and the failure of
  order eleven into an existence theorem with the same hypotheses.
- `.exists_exact_real` and `.exists_exact_realAlgebraic` are unconditional
  in \(\mathbb R\) and the field of real algebraic numbers. The real
  parameter construction selects the positive radicals of the source.
- `.exact_of_algClosed` needs only that the displayed integer \(D\)
  be nonzero in the algebraically closed coefficient field.
- `.exact_mod37` and `.exact_mod227` are two explicit positive-characteristic
  specializations. An additional theorem, `.exact_mod11_degree_four`,
  uses a concrete field of cardinality \(11^4\), obtained by adjoining
  two roots with checked quadratic nonsquare conditions. No positivity or
  real structure is used in any of these specializations.
- `.exact_nilpotent37` and `.exact_nilpotent227` cover all nontrivial
  commutative rings in which the corresponding prime is nilpotent.
  This includes every ring of characteristic a power of that prime,
  without a completeness, local-ring or field hypothesis. A Newton
  lift squares each residual in the nilpotent principal ideal and
  checks that the necessary inverses remain units.

There is no rational upper-bound improvement here, and no claim over
all rings in which \(10!\) is a unit.

## From integer coordinates to ordinary rooted trees

Close the eight square-free coordinates in \(x,y,z\) with the three
exact multiplication relations. The source's two nested positive
radicals are \(z/21\) and \(zx(y-2)/63\); `source_radicals` verifies
these signs and squares over the reals. Every coefficient is scaled
by one common input denominator \(D\). The integer model's arithmetic
is proved to evaluate correctly in any target ring with the three root
relations. There are no assumptions that the coordinates are linearly
independent or that the target is a field.

For every reviewed tree \(t\), write
\[
 \boldsymbol V_t = \operatorname{forestFactorial}(t)\,
   \boldsymbol{\Phi}_t(A_{\rm num}).
\]
The two-argument constructor satisfies
\(\boldsymbol V_{t\triangleleft u}=\boldsymbol V_t
 \odot (|u|\,A_{\rm num}\boldsymbol V_u)\).
Thus identical normalized stage vectors of the same grade can be
merged. The exact cache retains 582 distinct profiles and 274
actions, with 1,328 grade-compatible joins. Each leaf, join, sparse
matrix action and paid weighted output is checked separately in
Lean. The finite-closure theorem covers every reviewed tree by
structural induction, regardless of its particular binary
presentation. Scaling the matrix and output weights by \(D^{-1}\)
then restores the ordinary normalized equalities.

Independently, the Python replay checks all 1,205 ordinary rooted trees
through order ten using integer tuples throughout. Its role is data
generation and independent verification, not a premise of the Lean
theorems. The eleventh-order bush output is different: multiplying
its normalized discrepancy by \(52920\) gives exactly \(1\). This
proves exactness even when a field or residue-field coefficient map
is used.

## Replay

From the present directory, with Python 3:

    python3 generate.py

From ai-generated/lean with the matching Mathlib checkout:

    lake build +RKCert.ReviewedNative.ERK10StepanovReal +RKCert.ReviewedNative.ERK10StepanovFields

To regenerate the source fixtures from the authenticated input:

    python3 generate.py --emit /path/to/lean/RKCert/ReviewedNative
    python3 generate_vector_cache.py --emit /path/to/lean/RKCert/ReviewedNative
    python3 generate_class_checks.py --emit /path/to/lean/RKCert/ReviewedNative
    python3 shard_expensive_checks.py --emit /path/to/lean/RKCert/ReviewedNative \
      --legacy legacy-completed.list --parts /tmp/erk10-parts.list --blocks /tmp/erk10-blocks.list

The last script uses individual named receipts for the expensive blocks,
and splits large join rows into twelve-column checks, reducing peak memory.
It leaves the faster original blocks unchanged according to the checked
manifest.

The accompanying Lean audit reports the exact endpoint axiom lists.
The generated arithmetic receipts use `decide +kernel`, not the
trusted-compiler checker. The separately recorded matching toolchain
is the one actually tested; this does not claim a full dependency
build across other Lean releases.
