# Source and kernel receipt

The 85 project source files actually imported by
**RKCert.ReviewedNative.DIRK12MidpointRealExactOrderAudit** are listed in
dependency order in [project-source-closure.tsv](project-source-closure.tsv).
The columns are Lean module name, repository-relative source path, and
SHA-256 of the exact source used. The previous grouped, low-adjoint, and
forward-fit modules are included. The direct nonproject imports are
recorded in [external-imports.tsv](external-imports.tsv); their versions
are fixed by the toolchain and package locks recorded in
[toolchain-locks.txt](toolchain-locks.txt).
The precise output of the separately compiled typed audit is
[lean-4.36.0-axioms.txt](lean-4.36.0-axioms.txt).

For an integrated repository checkout, regenerate the two closure files
with the same checkout in all three source positions:

    R=ai-generated/research/dirk12-fifteen-midpoint-native-real-exact
    python3 -B "$R/source-closure.py" . . . /tmp/dirk12-external-imports.tsv \
      RKCert.ReviewedNative.DIRK12MidpointRealExactOrderAudit \
      > /tmp/dirk12-project-source-closure.tsv
    cmp "$R/project-source-closure.tsv" /tmp/dirk12-project-source-closure.tsv
    cmp "$R/external-imports.tsv" /tmp/dirk12-external-imports.tsv

## Composition with the existing checked lower bound

The unconditional width theorem
**RKCert.Paired.dirk_order12_charZero_field** is already in
[DirkGradeSix.lean](../../lean/RKCert/DirkGradeSix.lean), with
[its recorded native axiom audit](../../release-compatibility-b083e10/verified/v4.36.0/AuditDIRKGradeSix.log).
It holds over every characteristic-zero field, so it specializes to the
reals without ordered-field assumptions. It uses the older cleared
**HasTreeOrderAtLeast** predicate. The explicit
[reviewed order equivalence](../../lean/RKCert/ReviewedOrderBridge.lean)
transports the same physical matrix, output weights, and tree order with
no field assumption. For a reviewed-order real candidate of width \(s\),
the lower argument is exactly

~~~lean
have l : RKCert.Paired.LowerArray A := by
  intro i j e
  exact ha (show i < j from e)
exact RKCert.Paired.dirk_order12_charZero_field l
  ((RKCert.ReviewedOrderBridge.hasOrder_iff A b 12).1 ord) (by decide)
~~~

Here **ha** is the literal lower-triangularity premise and **ord** is
the reviewed **HasOrder 12** premise. This lower endpoint and the new
15-stage upper give minimum 15 over the reals. The same mathematical
minimum over the real algebraic coefficients uses the separately audited
degree-216 field model. The transitive source closure here is for the
new complete upper audit; this receipt does not assert a fresh joint
build of the old lower closure or a typed degree-216 realization.
