# The dormant opposite-plateau alias has no zero left initial slope

**Scope.** In the [sparse ERK11 plateau-alias chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md), take \(q=10,n=12\), both plateau pairs full, and the only dormant middle stage physical 9 at \(\zeta=d\). This excludes the **whole first exceptional mask**, the vanishing raw left initial slope. It uses the inherited ordered mixed-moment guards to measure the central alias, and otherwise is an exact characteristic-zero width-field proof. Reflection gives the corresponding mask on the mirrored \(\zeta=a\) chart. It does not close the other five masks, the other aliases or the unrestricted stage interval.

## 1. Exact 12-dimensional width reduction

Let \(D_L^0,D_L^a\) be the left derivative rows and \(D_R^1,D_R^d\) the reflected derivative rows. At \(\zeta=d\), the actual anchored reverse row \(R_9\) is a live multiple of \(r_d\), because \(J_0=b_9p_9r_9>0\) supplies its measured primitive amplitude. Put \(\ell_j=[D_L^j,r_d]\) for \(j=0,a\) (write \(\ell_1\) for the latter). The actual left boundary row is proportional to
\[
 (a-u)(a-v)D_L^0-uvD_L^a,
 \qquad (u,v)=(c_6,c_7).
\]
Thus its actual off-diagonal with row 9 forces \( (a-u)(a-v)\ell_0-uv\ell_1=0\). In the mask \(\ell_0=0\), the live \(uv\) gives \(\ell_1=0\). The scalar relation does not assume a derivative ratio in this zero branch.

Pairing with \(r_d\) using the rational inverse Gram gives, after removing its live reflected endpoint factor,
\[
 \ell_0\ \propto\ 3-32d+108d^2-144d^3+66d^4 .
\]
Use the exact diagonal width equation \(\mathcal D(a,d)=0\) from the [central alias proof](ERK11-NONZERO-TEN-TWELVE-SYMMETRIC-CENTRAL-ALIAS-EXIT.md#1-a-reciprocal-diagonal-gives-a-width-only-equation). Form the two exact resultants in \(d\) of \(\mathcal D\) with \(\ell_0,\ell_1\), removing only exact powers of the already live width factors \(a,d,d-1,a-d\) from the slope inputs. The resultants have degrees 32 and 80 in \(a\), and their common factor is \(a^4H_{12}(a)\), where
\[
\begin{split}
 H_{12}(a)={}&29947500a^{12}-156816000a^{11}+363884400a^{10}
 -493307520a^9+433718388a^8-259591392a^7\\
 &+108028376a^6-31362048a^5+6277059a^4-841392a^3
     +71496a^2-3456a+72 .
\end{split}
\]
It is irreducible in the exact rational factorization. The root \(a=0\) is forbidden by the front. Over the exact field \(\mathbb Q[a]/H_{12}\), the three width equations have **linear gcd** in \(d\). Thus the actual second width is its single root \(d_*\) in that number field; no further embedding, ordering of real roots, or special finite-place choice is needed. The exact replay checks the three evaluations at \(d_*\) and the nonzero inherited width and primitive denominators.

## 2. An actual row-11 fallback, not the redundant outer width law

The exact width field above retains the previously measured \(\widehat L\), a live representative of actual \(L_9\) (using \(p_9=\) the paid central primitive from the width conditions). On the right, take **this \(L_9\)** as the opposing row, not a left derivative direction. Put
\[
 r'_0=[\widehat L,D_R^1],\qquad r'_1=[\widehat L,D_R^d].
\]
Both are nonzero in the whole exact degree-12 width field at \(d_*\), verified before any division. Therefore \(r'_1D_R^1-r'_0D_R^d\) is a live representative of the **actual \(R_{11}\)**: it follows from \([L_9,R_{11}]=0\) and the actual derivative formula for that physical row. This does not infer a synthetic right row from the zero left slope.

Now use the newly measured \(R_{11}\) as the **left** opposing row. Its two pairings with \(D_L^0,D_L^a\) are both live in the same exact field. The left seventh-row off-diagonal \([L_7,R_{11}]=0\) gives the left unordered extra hull using these new slope coefficients, even though the two pairings against \(R_9\) vanish. For the outer-stage constraints one uses the actual **\([L_8,R_{11}]=0\)** and **\([L_9,R_{10}]=0\)**. These are physical inverse-Gram row relations in the common mixed grade-five chart; the literal primitives still vanish through 8 and from 10, respectively. No ordinary reverse order eleven is used.

Apply the exact [sparse two-flank fit](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md#2-a-sparse-fixed-moment-block-and-an-affine-product-equation) with these two *new* opposing rows. The same three rank-zero moment rows for \(Q\) are paid because \(\zeta=d\), and both two-pair first/second pool calibrations are unchanged. Before the sparse divisions the replay checks each rotated fixed moment determinant and raw affine slope is live at \(d_*\), including the normalizations of the two first-pool lines. Thus every unordered extra product and required first-pool line is determined by the two legal rotated fits. There is no root of \(Q\) or stage weight in any denominator.

The two physical affine first-pool lines must still be proportional (the right response differs only by the single live scale). The required determinant, calculated in the exact width field at \(d_*\), is a **nonzero polynomial residue of degree 11** modulo \(H_{12}\). Since the quotient is a field, this cannot vanish in any coefficient-field extension. Thus the entire left initial-slope zero mask is excluded. This uses neither a redundant direct \(S(x)=0\) constraint on the slope-zero widths nor the already proved proportionality of the two \(Q\) profiles.

The standalone replay recomputes the exact rational resultants, the width field gcd, every fallback unit and the final nonzero residue. The adjacent Lean file checks the forward scalar projective direction and the field implication from a vanished first slope to the vanished second slope. The actual inverse-Gram and polynomial width-field ingress remain mathematical.

The [standalone exact replay](erk11-plateau-alias-left-slope-exit/replay_erk11_plateau_alias_left_initial_slope.py) and [Lean scalar gate](../lean/RKCert/ReviewedNative/ERK11InitialSlopeFallbackGate.lean) were independently checked, the latter on all four targeted versions.
