# The regular star–star zero-tail interior placements

For ten-stage strict SDIRK8, take the [constant numerator at nine distinct reverse sites](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) with the first stage the sole quadratic-defect row, ordinarily silent, and with eight ordinary active clocks distinct. The extra ordinarily silent stage has actual nonzero reverse read at its distinct ninth clock. Here it is physical **5, 6, or 7**. Assume the [regular mixed-quintic star-front/star-rear chart](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md), and suppose both centered star-tail coefficients vanish, (A=B=0). This packet excludes those three placements over every characteristic-zero field, with no ordering assumption. Other front/rear phases and the unrestricted **10–11** bound are unchanged.

The reusable [zero-tail polynomial identities](../sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail/README.md) require just the same two *literal* early star anchors, not their ordinary weights or the physical position of the extra silent row. The genuine quintic coefficient and the coprimality identity there force the homogeneous profile
\[
 H_g=-8P L_3+(162\gamma-45)Q L_4+5Q L_5
\]
and the full degree-five diagonal ((18\gamma-5)(1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1)=0). The scale denominator (H_g(\gamma A_0)) is nonzero by the actual nonzero literal amplitude. Normalize by that amplitude. The actual fourth fit (H(\gamma s)=H_4(s)) supplies the full cubic (S) after cancellation of only the exact padded roots (s=A_0,B_0). Both are genuinely forbidden because rows 2, 3, and 4 are ordinary distinct. The native file audits the new small structural identities; the chronology and finite arithmetic remain source-level.

Because the silent row lies strictly between physical 4 and 8, the **six known ordinary clocks** are (gamma A_0,gamma B_0,gamma s,x,c,d), where (x=1-\gamma), (m=1-2\gamma), (c=m-\gamma v), and (d=m+\gamma v). The monic ordinary nodal polynomial has degree eight, and is (E R) for the monic missing quadratic (R), where
\[
 E(X)=(X-\gamma A_0)(X-\gamma B_0)(X-\gamma s)(X-x)
     ((X-m)^2-\gamma^2 w),\qquad w=v^2.
\]
All six are already counted once, independently of the order of the two actual rear clocks. No hypothetical ninth ordinary clock and no collision associated with a missing node is required or divided out. Since the four nonconstant coefficients of degrees one to four of (H W_{ER}-ER W_H) vanish using ordinary precision **seven**, the four rows of the three columns for (E,EX,EX^2) annihilate the coefficients of (R). Every (3\times3) minor is zero. Every entry is affine in (w), so every minor has degree at most three.

At (p=1097,T_0=345), where (2T_0^2=1) and (T_0) denotes the front-orientation coefficient, the diagonal retains **all** components of degrees (1,1,1,2). The literal normalization and leading coefficient of the full cubic (S) are units. On every full cubic algebra, the first minor's cubic leading coefficient is a unit, and each other minor is a unit modulo that first monicized cubic. Every algebra is finite free over its predecessor and every inversion is checked in the complete reduced algebra, not at a guessed physical root. A reduced unit in a finite free algebra over the local coefficient ring lifts by the determinant of multiplication; hence the three successive root equations are impossible over any characteristic-zero extension. No square root of (w) is chosen, no assumption on the invisible defect, no fifth-stage gate, and no higher scalar precision is used.

Install `sympy==1.14.0` and `python-flint==0.9.0`, then run `python3 check_star567_zero_tail.py` from this directory; the explicit sibling helper list is in the entry point. The [Lean structural receipt](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStarInteriorZeroTail.lean) is separate from the Python arithmetic proof and is checked on Lean/Mathlib 4.36.0.
