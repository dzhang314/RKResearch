# Native DIRK initial two-seed obstruction

This leaf reuses the canonical strict one-seed chronological theorem,
rather than copying its proof. It gives the already-known DIRK
two-seed criterion with arbitrary triangular diagonal, on the human
reviewed tableau and the actual native forward and reflected stage
defects. It does not yet assert the subsequent rank counts.

Let \(N\) have a triangular leading-coordinate rule in either
chronology, and let \(Y\) multiply coordinatewise by a clock vector
\(\mathbf y\). For the input \(\mathbf v\), define
\[
\mathbf z \coloneqq Y\mathbf v,\qquad
\mathbf q_2 \coloneqq 2N\mathbf z-Y\mathbf z,\qquad
\mathbf q_3 \coloneqq 3NY\mathbf z-Y^2\mathbf z,\qquad
S\coloneqq 3(YN-NY).
\]
The diagonal parts of \(YN\) and \(NY\) agree at the first possibly
nonzero coordinate, so \(S\) is *strictly* causal. The paid seed
combination is exactly
\[
3Y\mathbf q_2-2\mathbf q_3=2S\mathbf z-Y^2\mathbf z.
\]
Moreover, \(\mathbf z\) lies in the coordinatewise image of \(Y^2\):
at a nonzero clock one uses \(\mathbf v_i/\mathbf y_i\) as the
\(i\)-th input, and at a zero clock both sides are zero.

A subspace invariant under \(N\) and \(Y\) is invariant under \(S\)
and \(Y^2\). If it contains both seeds, the strict one-seed theorem for
the pair \((S,Y^2)\) places \(\mathbf z\) in that subspace. No division
by the integers 2 or 3 enters this argument. The field is used only
to invert nonzero individual clock coordinates as the strict
causal theorem requires.

The two native applications are:
- `RKResearch.Certified.Graded.forward_dirk_seeds_force_nodes`,
  on the ordinary clock and the actual degree-two and degree-three
  monomial defects;
- `RKResearch.Certified.Graded.reverse_dirk_seeds_force_clock`,
  on the original matrix transpose, the reflected clock, and the
  physical D(2) and D(3) rows.

The audit also consumes both statements on the exact native order-six
tableau: if the invariant subspace annihilates the genuine paid
ordinary probe (respectively all rows in it annihilate the unit
column), then the forced clock vector contradicts the order-two
moment. These are no-plateau ingredients, not a claim of a finished
order-six stage count.

Build with Lean and Mathlib `v4.36.0`. The pinned direct inputs are
`CausalStage`, `ReflectedMoments`, and `ChangeCoefficients`.
Run `AuditReviewedNativeDIRKSeed.lean` and
`leanchecker --verbose RKCert.ReviewedNative.DIRKSeedReduction`
after building the one leaf. No old tree or order conversion is used.
