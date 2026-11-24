# Order-nine ERK physical reduction

Pinned Lean and Mathlib v4.36.0.

Relevant current theorem entry points for actual strict lower matrices
on twelve stages with HasTreeOrderAtLeast A b 9:

* RKCert.Paired.order9_actual_remaining_census, ordered fields:
  exactly one off-defect node, or five off-defect and six clean nodes.
* RKCert.Paired.order9_actual_five_six_atlas_input, ordered fields:
  the five-off/six-on chart forces a genuine distinct ordered-root
  tuple of the Jacobi pencil and the exact scalar K8 and terminal
  product zeros. All physical stage placement cases are checked.
* RKCert.Paired.order9_no_five_off_five_on, every characteristic-zero
  field: the entire fixed Radau five-off/five-on branch is excluded.
* RKCert.FixedFactor.order9_no_seven_off and
  RKCert.FixedFactor.order9_no_six_off_five_on, every characteristic-zero
  field: literal physical exclusions, no positivity assumed.
* RKCert.Paired.order9_no_six_off and
  RKCert.Paired.order9_no_eight_or_more_off, ordered fields:
  actual exclusions including the free-parameter six-on pencil.

The scalar local-prime norm/gcd for the remaining two-curve chart and
the separate one-off amplitude/terminal atlas still need Lean. This
is not a certificate of the numerical p9 >= 13 statement.
The p8 chart is already in the base snapshot and unchanged.

From this directory, check the two entry points:
    lake build RKCert.ERKOrderNineCensus RKCert.ERKOrderNineFiveSixAtlas
Both named leaves were independently replayed at the pinned release.
