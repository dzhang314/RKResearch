# The dormant plateau alias has no left fixed-moment pivot loss

**Scope.** In the [sparse plateau-alias chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md) with \(q=10,n=12\), both plateau pairs full, and sole dormant physical 9 at \(\zeta=d\), this excludes the third exceptional mask, the vanishing left fixed three-by-three moment determinant. Both initial-slope masks have already been excluded. The geometric and mixed-moment guards are those of the ordered-field chart. The new field-place computation works in characteristic zero with those guards supplied. Reflection transfers the calculation to the opposite plateau orientation. No claim is made about the separate right moment mask or unrelated affine-pivot losses.

## 1. Exact projection and finite-place ingress

Let \(\Delta_L\) be the left fixed determinant from the [sparse fit](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md#2-a-sparse-fixed-moment-block-and-an-affine-product-equation). Deflate only powers of the already live \(a,d,d-1,a-d\). The exact resultant in \(d\) of the reciprocal diagonal \(\mathcal D\) and this deflated determinant has degree 143 in \(a\), with irreducible degrees and multiplicities \(1^8,12,51,72\). The degree-one factor is \(a\), forbidden. In the degree-twelve field the exact two input equations have linear \(d\)-gcd, giving both left initial slopes zero; this is the [already excluded left-slope mask](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-LEFT-SLOPE-EXIT.md).

For each other irreducible factor \(F\), the replay finds a simple residue of its monic polynomial, with all its coefficients integral at the chosen prime, and checks that \(\mathcal D\) retains full degree 13 in \(d\). At the chosen residue of \(a\) the gcd in \(d\) of the two input polynomials is linear. Given any characteristic-zero candidate at \(F(a)=0\), the simple residue defines an embedding of the exact width field \(\mathbb Q[a]/F\) into \(\mathbb Q_p\) by Hensel. Extend this embedding to the algebraic \(d\) of that candidate. Its image is integral, since it solves \(\mathcal D\) with integral coefficients and unit leading coefficient. Every possible choice of \(d\) therefore reduces to the single root of the residue gcd, without assuming there is only one characteristic-zero \(d\) or that any unknown tableau entry can be reduced. All subsequent divisions are by units explicitly checked at these residues. It suffices to contradict a necessary polynomial or rational expression in those reconstructed widths and shapes.

## 2. The degree-51 factor: a real temporal row restores the pivot

In either orientation put \(h=w/2,\ \phi=X^2(w-X)\) and keep the measured unordered hull \(B=B_0+tB_1\), with \(t=uv/(w\ell_0)\ne0\). In the sparse coefficient coordinates
\[
 Q=U\phi+W X B_0+T X B_1+A(B_0+tB_1),\qquad
 P=w\left[U+\frac{T-tW}{t}(X-h)\right].
\]
The three paid scalar moment rows of \(Q\) plus the **actual outer row** are four homogeneous equations in \((U,W,T,A)\). The left physical outer row pairs \(L_8\) with \(R_9\); the right physical outer row pairs \(L_7\) with \(R_{10}\). These are actual mixed-grade-five off-diagonals, and use the already calibrated seventh and half-clock hits. The first three columns of this four-row system do not depend on \(t\); the last column is \(c_0+t c_1\). Thus the full determinant is \(g_0+t g_1\) by exact linearity. This determinant formula is valid even though the first three *moment-only* rows have determinant zero.

At the degree-51 place \((p,a,d)=(47,30,12)\), the left first-three-column block has a nonzero minor using **moment rows 0 and 1 and the temporal outer row**. The right first-three-column moment block is live. On both flanks \(g_1\ne0\), so the actual products are \(t=-g_0/g_1\), reducing to \(9\) and \(28\). The repaired left pivot and the guarded right pivot also show that \(A\) cannot vanish in a true nonzero kernel. Normalize \(A=1\) and solve for the other three entries with the specified minors. This is a single true profile line on each side. The two affine first-pool lines are necessarily proportional in the physical coordinate, so with the right still in the reflected variable their coefficient determinant must be
\[
 p_0 q_1+p_1(q_0+q_1)=0 .
\]
It reduces to \(37\ne0\bmod47\). No right pivot is presumed live from the left moment loss.

## 3. The degree-72 factor: use the original outer response, not the lost determinant

At the degree-72 place \((p,a,d)=(17,5,14)\), the right moment block, right \(g_1\), right \(t\), geometry and normalization guards are live. Recover the right profile with \(A=1\); the replay does not require any left temporal/moment pivot. The measured reverse response differs by a single live scale from the physical one. Therefore reflecting the right profile to the physical variable gives the left affine first-pool line \(P\) up to a scalar and the second-pool line up to another scalar. Calibrate their relative scale at the actual left singleton \(h=a/2\) using \(Q(h)=P(h)f_L(h)\), with \(f_L=X^2(a-X)/a\). Both coefficient-line evaluations at \(h\), and the two evaluations at the active outer singleton \(x=c_8\), are checked as units at the residue.

The original anchored outer relation from \([L_8,R_9]=0\) precedes the sparse determinant. Write its adjusted scalar model as \(X(X-a)E(X)\), and use \(B(0)=tB_1(0)\) and the prior correction \(B(0)S(X)=S_0(X)+tS_1(X)\). The actual sample \(Q(x)=P(x)F_x\) then gives
\[
 k_0+t k_1=0,\qquad
 k_0=Q(x)S_0(x),\quad
 k_1=P(x)x(x-a)E(x)B_1(0)+Q(x)S_1(x).
\]
This recovers the true left product from the right profile even if the previous left determinant supplies no live slope. The residue is \((k_0,k_1)=(1,13)\), so \(t\equiv13\bmod17\).

Now the true calibrated left triple \(h,u,v\) consists of distinct roots of \(Q-P f_L\) and has monic hull \(B_0+tB_1\). The remainder modulo this monic cubic must be zero, and monic remainder commutes with the residue operation regardless of possible collisions of particular roots modulo 17. The replay instead obtains
\[
 (Q-P f_L)\bmod (B_0+tB_1)=7X^2+7X+11\quad\text{over }\mathbb F_{17}.
\]
This closes the last left-moment factor without an assumption on the old left affine pivot, nor a claim about affine losses at other widths.

The standalone rational replay computes all projection factors, the small exact field, simple place and leading-coefficient checks, the literal sparse equations in each residue, and the two terminal contradictions. The adjacent core Lean checks the division-free outer-product relation and the cleared modular remainder identity. The actual grade payments, width-field projection and Hensel bridge are proved in the notes/replay, not yet in Lean.

The [standalone exact replay](erk11-plateau-alias-left-moment-exit/replay_erk11_plateau_alias_left_moment_pivot.py) and [Lean scalar gates](../lean/RKCert/ReviewedNative/ERK11LeftMomentFallbackGate.lean) were independently checked, the latter on all four targeted versions.
