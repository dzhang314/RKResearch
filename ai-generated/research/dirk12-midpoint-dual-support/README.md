# Complementary-support criterion for order twelve

The checked theorem turns actual low forward and reverse support information
into the reviewed all-rooted-tree condition. It works over any commutative
ring in which the small reverse integers are units; it assumes neither an
ordered field nor nonnegative weights.

- Forward bands of grades 0–2 are zero. Through grade 5, they are supported
  where the output weight is zero, and contain the real forward defects.
- Reverse bands through grade 5 are zero on those coordinates and satisfy
  the actual transpose recurrence and reflected clock recurrence, with all
  scalar orthogonalities paid at total degree at most 11.
- At grade 6 only the forward matrix action on grade 5 and the scalar
  quintic primitive require extra bridge tests.
- Exact ordinary scalar moments imply the mixed scalar moment identity by
  a division-free induction; no analytic integration lemma or degree-twelve
  moment is assumed.
- From grade 6 onward the forward flag is the annihilator of the
  complementary reverse band and reflected weighted scalar moments.
  Every permitted nonlinear product of two nonzero defect bands has a factor
  supported on the ghosts. Its product is automatically in the high band.

Source: RKCert/ReviewedNative/DualSupport12.lean. The endpoints are
LowChecks.hasOrder and mixed_scalar. The separate typed audit imports the
source and checks both conclusions against the repository's actual
HasOrder. Build the module from ai-generated/lean with its normal Mathlib
and reviewed sources, and run AuditDIRK12MidpointDualSupport.lean against
the resulting module. The included replay is Lean 4.36.0; no other matched
Mathlib/toolchain pair was replayed for this file. There is no custom axiom,
compiler oracle, or Lean proof of the specific degree-216 tableau in this packet.
