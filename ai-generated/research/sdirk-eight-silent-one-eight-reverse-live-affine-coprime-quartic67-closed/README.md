# Affine-coprime quartic: actual sixth silent or actual seventh silent

This excludes two separate placements in the [strict ten-stage SDIRK8 affine-coprime quartic chart](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed/README.md), each with both literal front phases and both ordinarily active eighth rear phases. The field has characteristic zero. Physical one is the sole nonzero quadratic-defect row, ordinarily and reversely silent. The eight ordinary physical rows have distinct clocks and the additional ordinarily silent row \(\zeta\) has actual nonzero reverse weight at a distinct ninth clock. The reverse numerator \(T\) is nonconstant affine, the mixed numerator \(S\) has degree at most four, and \(S,T\) are coprime. It follows that \(S\) is proportional to shifted \(L_4\) and the true normalized cubic-defect profile is \(H(X)=\gamma\Delta L_4(X)/Q(X)\), as in the companion. No ordering is used. The unrestricted **10–11** interval remains unchanged.

## The cases share the actual ordinary fifth but not the later assignment

In \(\zeta=6\) the two ordinary clocks not already fixed as pegs are \(c_5,c_7\). In \(\zeta=7\) they are \(c_5,c_6\). In **both** cases \(a=c_2,b=c_3,q=c_4,x=c_{10},c=c_9,d=c_8\) are the six true ordinary pegs, including the ordinarily active eighth. The same ordinary fourth \(J(\gamma,s)=0\), true rear shape \(F(\gamma,u)=0\), and six-peg coefficient determinant \(P=0\) of the [silent-fifth projection](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic5-closed/README.md#a-small-homogeneous-ordinary-determinant) apply. Reuse its full exact gap projection \(N\) and monic diagonals of degree **144** or **264**. The needed nonzero factors and leading cases are unchanged. We **do not** reuse that packet's final ordinarily silent fifth constraint: here actual fifth is ordinary, and the distinct actual silent clock neither is an ordinary peg nor is set equal to fifth or to the unknown other ordinary root. No tap, amplitude, or transported read at sixth or seventh is exchanged between the cases.

## Recover the actual missing quadratic without selecting a root

Retain only the first five ordinary pegs \(a,b,q,x,c\) for the [five-row Padé-style Cramer reconstruction](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed/README.md#full-finite-fibers-and-actual-fifth) of the actual monic ordinary \(D_8\). The relevant identity is the paid-precision-seven
\[
 L_4 W_{D_8}-D_8 W_{L_4}=\lambda Q^2 .
\]
The five rows determine the unknown cofactor coefficients and the scale of \(Q^2 W_{L_4}^{-1}\bmod L_4\) wherever their determinant is a unit. This **fixed** determinant is checked as a unit in the full finite reduced algebras, not inferred from a generic clock choice. Sixth peg \(d=c_8\) is not used for this solve.

Now divide monically by the product of **all six** ordinary pegs. Across the projection algebra this can have a nonzero remainder; the replay retains the remainder entries as additional necessary zeros, rather than claiming each projected point is an actual nodal polynomial. At a true tableau the quotient must be the monic missing quadratic, with the two ordinary roots listed above, and the remainder zero. Such monic division does not assume the other ordinary root, or distinct roots after reduction. A coincident or repeated reduced root is still included.

Physical fifth satisfies the same actual rows 2–5 determinant with its true normalized ordinary amplitude \(H(\gamma Y)\), \(Y=c_5/\gamma\). Clear the actual denominator \(Q(\gamma Y)\) and divide only by the true nonzero literal pads \(Y-A,Y-B,Y-s\), exactly as in the literal 2/3 companion. This gives \(J_5(Y)\) of degree at most two. At normalized missing quadratic \(Y^2+r_1Y+r_0\), write \(J_5(Y)=a_0+a_1Y+a_2Y^2\) allowing zero top terms. Put \(\alpha=a_0-a_2r_0,\ \beta=a_1-a_2 r_1\). The full multiplication determinant on the missing quadratic is
\[
 \alpha^2-\alpha\beta r_1+\beta^2r_0 .
\]
Indeed its difference from \((\alpha+\beta Y)(\alpha-\beta Y-\beta r_1)\) is \(\beta^2(Y^2+r_1Y+r_0)\). Hence the determinant vanishes at any true common root, with no choice between the two ordinary assignments. The exact replay independently checks it matches the two-dimensional multiplication determinant, including when the fifth gate drops degree.

## Complete finite verification

Use the full monic diagonal reductions at \((1129,t=203)\) from the six-peg projection. Every factor, with multiplicity, is retained. The ordinary rear shape and the ordinary fourth retain their full leading units. Over each full reduced gap gcd and fourth quadratic the fixed Cramer determinant and earlier literal stage denominators are units. The ordinary determinant \(P\), the six-peg remainder entries, and the last multiplication determinant generate a unit. This is tested on **all 37 complete components** (4, 19, 4, 10), with weighted gap/fourth dimensions 576, 528, 576, 528. The finite integral algebra argument from the literal companions lifts these checks to characteristic zero; no hypothesis of good reduction of a specific tableau is made.

The contradictions occur at actual physical fifth, so each placement \(\zeta=6\) or \(\zeta=7\) is excluded before any use of their different physical sixth and seventh rows. Combined with the literal 2–5 packets, this leaves only **ordinary silence at physical eighth** in the scoped affine-coprime quartic family. Other reverse numerator degrees, a genuinely quintic \(S\), and other support charts are not covered.

## Replay and Lean

With `sympy==1.14.0` and `python-flint==0.9.0`, run `python3 check_eight_reverse_live_affine_coprime_quartic67.py` beside the earlier literal companions. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineQuarticOrdinaryFifth.lean) verifies the true monic quotient and degree-robust common-root determinant over arbitrary commutative rings. These checked on Lean/Mathlib 4.36.0; the chronology and exact finite arithmetic remain source-level, and the full exclusion is characteristic zero.
