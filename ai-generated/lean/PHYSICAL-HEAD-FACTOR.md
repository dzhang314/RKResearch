# A paid disjoint head cannot divide the Lobatto factor

**Theorem and scope.** Let K be any characteristic-zero field. Let A,b be
the original lower-triangular tableau with tree order at least 2m on
3m−3 physical stages, where m=7 or 8. Let P divide the native signed
Lobatto polynomial G_m. If j+2≤m, there is no actual grade-j ordinary
trace θ with polynomial companion XP for which every midpoint defect
vanishes at each physical index where θ is nonzero. In particular, if
deg P≤n and n+3≤m, there cannot be a genuine grade-n defect that matches
P(c_i) on all rows where any midpoint defect is nonzero. These are
conditional *physical tableau* contradictions, not new unconditional
stage floors. In particular, extraction of P and its dirty-row mask
from other rank hypotheses is not assumed accomplished by this packet.

## Proof

The factor P is nonzero because G_m has degree m. More generally,
consider any grade-j ordinary trace θ with nonzero polynomial companion
F. For a nonzero spectator G, suppose all output-active nonzero θ
coordinates were roots of G. The actual weighted sums pairing θ with
G X^k would vanish. By the genuine trace pairing, these sums are the
formal integrals of FG X^k. Paying every k up to deg(FG) forces FG=0
by shifted-Hilbert nondegeneracy, contrary to F,G being nonzero. The
precise needed budget is j+deg G+deg(FG)+1≤p. This support escape
does not divide by a stage weight or discard any zero-weight row.

For F=XP take G=X−1. The budget holds since deg(XP)≤j≤m−2.
The earned weighted witness with c_i≠1 lies strictly before the
actual last stage, whose clock is 1. The globally first nonzero θ
coordinate i is therefore not the last. At that row the genuine
commutator (CA−AC−A²)θ is a defect of grade j+2≤m. Its value
is −A_ii² θ_i by triangularity and first support. Midpoint cleanliness
forces it zero, and thus A_ii=0. Hence (Aθ)_i=0. The true trace of Aθ
agrees there with the primitive of XP, so J(XP)(c_i)=0; this is
deduced from the actual tableau, not hypothesized.

At the same clean row the original trace gives θ_i=c_i P(c_i)≠0.
In particular c_i≠0. The true last-row cardinal, not an arbitrarily
chosen endpoint, forces each nonlast midpoint-clean row to be a zero
of G_m. Finally deg P+1=deg(XP)≤j≤m−2, so deg P≤4 at m=7 and
≤5 at m=8. The independently checked fixed-factor theorem says the
first primitive J(XP) is nonzero at *every* such nonzero root. This
is the required contradiction, also for repeated clocks, and without
an ordering on K.

For the interpolation-mask version, suppose w in the true defect
space at grade n agrees with P(c) on every midpoint-dirty row.
The vector P(c)−w is an ordinary trace of P and is zero on all such
rows. Multiplication by the stage clock gives a grade-n+1 ordinary
trace of XP supported only on real midpoint-clean rows. The first
theorem applies. Neither mask values on clean rows nor a primitive
equation are required by this version.

## Navigation

The namespace for the two physical conclusions is
RKCert.Paired.Terminal. The exact names are no_clean_head_lobatto_factor
and no_lobatto_factor_mask_on_dirty. The general polynomial support
escape and first-pivot primitive are separately exported as
RKCert.Paired.OrdinaryTrace.exists_weighted_active_outside_roots and
primitive_zero_at_first_clean. The remaining declaration is
Terminal.lobatto_zero_of_clean_nonlast.

The proof reuses the project's OrdinaryTrace.pair_polynomial,
primitive_shift_detect, physical commutator and triangular first-entry
formulas, last_physical, and previously verified fixed-factor moments.
Mathlib provides ordinary degree and evaluation arithmetic, the
finite-sum reasoning, and the field and nilpotence simplifications.
No finite-field computation or large tables are duplicated here.
