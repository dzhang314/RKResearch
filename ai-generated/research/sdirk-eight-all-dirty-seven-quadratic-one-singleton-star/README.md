# No three-singleton star opposite a doubled endpoint

Consider a strict ten-stage SDIRK method of ordinary order at least eight over a characteristic-zero field. Assume every physical quadratic defect is nonzero, there are exactly seven distinct clocks, and the two physical endpoint labels consist of one singleton and one double. In the actual orientation starting at the singleton, the first three rows **cannot all be singleton with a literal star third row**. This result needs no ordering or sign restrictions. A three-singleton arithmetic opener and the other singleton-end types are separate cases; no stage interval changes.

## The front star fixes the whole graph

Use the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) and [constant and affine exclusions](../sdirk-eight-all-dirty-seven-affine-final/README.md) to take the singleton graph \(R\) genuinely quadratic, \(Q/B=L_3-F_*L_4\) with \(F_*\) affine and nonconstant, and \(Q=P R\) up to the harmless scalar in \(Q/B\). The cubic \(P\) has the three distinct doubled labels. The quartic \(H=L_4-R(A_2+BR)\) has all four singleton labels. Swapping the two orientations here means the true weighted mirror; the nonzero physical weights of this all-dirty census guarantee that it is defined.

Normalize the diagonal to one. Use \(y=x-1\), \(m=1/(2\gamma)\), \(h=m-1\), so \(t=y-h\) is the centered coordinate. The actual endpoint labels are \(y=0\) and \(y=2h\), with \(h\ne0\). At the front, the [literal first-three star](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) with gap \(u\) has the normalized clock offsets \(0,u,2-u\) and defects \(1/2,\kappa(u)/2,\kappa(u)/2\), where \(\kappa(z)=1+2z-z^2\). The genuine guards are \(u,u-1,u-2,\kappa(u)\ne0\). Since every one of those labels is singleton, the quadratic \(2R(y)\) agrees with \(\kappa(y)\) at those three distinct abscissae, including \(\kappa(2-u)=\kappa(u)\). Thus
\[
        2R(y)=1+2y-y^2,\qquad W(y)=y^2-2y-1 .
\]
Nothing about the free gap \(u\) is imposed at this step other than the actual guards.

Use
\[
    L_3=(y-h)^3-\tfrac35m^2(y-h),\qquad
    L_4=(y-h)^4-\tfrac67m^2(y-h)^2+\tfrac3{35}m^4.
\]
Consecutive Legendre coprimality and \(W\mid Q\) imply that \(L_4\) is a unit modulo \(W\). Hence \(F_*=(L_3/L_4)\bmod W\) is the unique affine remainder, and
\[
             \mathcal P=(L_3-F_*L_4)/W
\]
is cubic with the actual three D labels. The terminal D label satisfies \(\mathcal P(2h)=0\). In particular this criterion **does not** divide by \(W(2h)\): an actual common doubled/graph-root label remains legal in the ingress. Clearing only the observed nonzero guards leaves a single irreducible constraint
\[
       8h^9-144h^8+858h^7-1858h^6+402h^5+2538h^4
                      -389h^3-1017h^2-78h+57=0 .
\]
The remaining two D labels are the roots of the monic quadratic \(\Delta\) obtained by deflating the known root \(2h\). There is no assumption that they split in the ground field.

## All actual rear possibilities

The physical rear triple, read in weighted mirror, starts at the double and consists of three distinct clock labels. Only one of its later clock labels can be singleton, because the disjoint front triple already uses three out of the four singleton rows. In particular rear D,S,S is impossible by the count, not by any unproved symmetry. Check the remaining literal phases as follows.

**Both later rear labels D.** Let \(\sigma\) be the sum of the two roots of \(\Delta\). The true rear star would give \(\sigma=4h-2\), by the reflection \(y'=2h-y\). The true rear arithmetic with the second label \(d\) in original coordinates would put the third at \(2d-2h\), so \(d=(\sigma+2h)/3\) and \(\Delta(d)=0\). These tests already cover both orderings of the two unknown D clocks. In the exact degree-nine field, neither equation holds.

**One later D and one S.** Let \(s\) be the original coordinate of that last singleton. The four singleton labels in \(H\) are \(0,u,2-u,s\), and \(H\bmod W=L_4\bmod W\). The quadratic factor \((y-u)(y-(2-u))\) reduces to the nonzero scalar \(\kappa(u)\). Consequently
\[
      L_4\bmod W \quad\text{is a nonzero multiple of}\quad
      y(y-s)\bmod W = 1+(2-s)y .
\]
If \(L_4\bmod W=l_0+l_1y\), this requires \(l_0\ne0\) and \(s=2-l_1/l_0\), entirely independent of the front gap. This displays how the \(l_0=0\) case would contradict the nodal equation, rather than merely dividing it out. The actual extra D clock must therefore be one of
\[
   d=(s+2h)/2 \quad(\text{arithmetic, second row D}),\qquad
   d=2(s-h) \quad(\text{arithmetic, third row D}),\qquad
   d=4h-2-s\quad(\text{star, either order}).
\]
The exact degree-nine replay shows \(\Delta(d)\ne0\) for each. This eliminates both literal star orders without claiming arbitrary row interchange preserves order. No unknown terminal residual scales or extra matrix bases are used. All tests are exact over the abstract irreducible field, so the conclusion holds over its every embedding and every characteristic-zero field even if the graph roots are nonsplit.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_star.py` (SymPy 1.14, python-flint 0.8). The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticOneSingletonStar.lean) verifies only the fixed quadratic and nodal remainder scalar gates. The rooted-order ingress and exact degree-nine replay remain a mathematical proof with independent computational verification, not a full native Lean theorem.
