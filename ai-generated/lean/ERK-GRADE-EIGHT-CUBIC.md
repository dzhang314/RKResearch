# Native closure of the grade-eight outside-core cubic branch

Over an ordered field, the first physical branch of the native grade-eight
frontier is no longer open. No old matrix, rooted-tree or RK order theorem
is used.

- `ERKGradeEightCubicChronology` consumes an actual grade-three multiplier
  and the native F5→F8 chart. It labels the finite pairs (clock, multiplier
  value), uses the checked logarithmic lane's `first_unmatched_block` on
  those labels, and builds a paid grade-eight residual with the real
  chronological predecessor values. One nonzero physical clock u must
  satisfy I(XP²)(u)=0, where deg P≤3 and P is nonzero. This part works in
  any characteristic-zero field.
- `OrientedCubicMoment` is only polynomial. A checked rational four-square
  identity for weighted monomials, with positive pivots 1/2, 1/36, 1/600
  and 1/9800, shows I(XP²)(u)>0 for every u≠0 in an ordered field. The
  rescaling uses u², so this does not assume positive clocks. No arithmetic
  leaf, numerical integration or determinant is computed or replayed.
- `ERKGradeEightCubic.grade_eight_third_inside_core` therefore forces the
  whole actual third defect space into the intrinsic core. The follow-on
  `grade_eight_remaining_two_cases` has only two branches left: the native
  flat rank-four 4→8 quartic chart, or a core of rank three that equals F4,
  contains an actual rank-two F3, and is already closed under coordinatewise
  multiplication. The off-mask count for the latter and the two-pivot
  quartic for the former are not supplied here. A uniform F8≥9 theorem
  or a p17 bound of 27 is not claimed.

The proof uses the exact 91f4a reviewed snapshot, the prior native grade-eight
frontier, and the checked logarithmic packet only for its chronology
selector. Run `python3 checks/run_small.py` for named build, independent
kernel replay and native width-26/negative-endpoint clients. All changes are
additive under this isolated staged tree.
