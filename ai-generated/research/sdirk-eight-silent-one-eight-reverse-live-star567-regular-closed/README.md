# The regular star–star interior silent placements with nonzero tail coefficient

Consider the [constant nonzero nine-site reverse numerator](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) for strict ten-stage SDIRK8. Physical stage one is the sole quadratic-defect row and has zero ordinary weight. The eight ordinary stages have nonzero weights and distinct clocks. The other ordinarily silent stage has actual nonzero reverse read at its own ninth distinct clock, and is physical **5, 6, or 7**. Suppose the regular genuine mixed-quintic star-front/star-rear chart, with both early quartic evaluations and the fourth-anchor denominator nonzero. This packet treats \(B\ne0\) in the centered tail \(A+Bv^2=0\). It is separate from the [identically zero centered tail](../sdirk-eight-silent-one-eight-reverse-live-star567-zero-tail/README.md).

## Exact diagonal projection

Let \(a=\gamma A_0,b=\gamma B_0,q=\gamma s\) be the actual literal clocks \(2,3,4\). Write \(x=1-\gamma,m=1-2\gamma,c=m-\gamma v,d=m+\gamma v,w=v^2,k=2-w\). All six clocks \(a,b,q,x,c,d\) are ordinary and distinct. The sole extra silent row is not an ordinary peg. If \(E\) is the product of their six monic linear factors, the ordinary degree-eight nodal polynomial is \(ER\) with \(R\) a monic quadratic. The four nonconstant coefficient rows in the [deflated Bézout identity](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md#1-deflate-only-the-actual-extra-reverse-clock) give a \(4\times3\) coefficient matrix for \(E,EX,EX^2\), with the coefficients of \(R\) in its kernel. The four \(3\times3\) minors vanish. This uses only ordinary scalar precision **seven**.

The [regular projection](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md#rear-star-exact-centered-square-projections) folds each minor homogeneously by \(A+Bw=0\). Its exact guards, already removed there, are powers of the nonzero \(\gamma,L_4(a),L_4(b)\) and the normalized regular fourth-anchor denominator. All four resulting polynomials are exactly odd in the orientation coefficient \(t\), \(2t^2=1\). Removing their common scalar \(t\ne0\) makes them rational for both actual star orientations. Call the primitive rational polynomials \(J_0,J_1,J_2,J_3\), with true \((\deg_s,\deg_\gamma)=(18,55),(17,54),(16,54),(16,54)\).

The exact \(s\)-resultants of \(J_0\) with \(J_1,J_2\) have \(\gamma\)-degrees **1871,1810**. Remove only their exact powers \(\gamma^{310},\gamma^{302}\), since the strict diagonal is nonzero. Their exact rational gcd has degree **1213**. The optional independent \(J_3\) resultant has degree 1816 and exact forbidden power \(\gamma^{316}\), and leaves the same gcd. The source computes and verifies the product of the ten primitive diagonal factors. By default it reconstructs the exact integer resultant coefficients by bounded CRT, not by guessing a degree from a residue search. The Sylvester coefficient \(1\)-norm is bounded by \(\|J_0\|_1^{\deg_s J_i}\|J_i\|_1^{\deg_s J_0}\) by the product of row norms, and the \(\gamma\)-degree bound is the sum of the crossed bidegrees. The CRT product is strictly greater than twice the bound, and each prime retains both \(s\)-degrees. Centered representatives therefore recover the exact integer determinant.

## Two distinct actual fifth-stage gates

Use the exact cleared profile \(H_*\) and correspondingly cleared scalars \(A,B\) after removing the common nonzero scale \(\gamma L_4(a)L_4(b)\). The [actual fifth-row determinant](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md#3-full-quartic-exclusion-and-conditional-pure-quintic-control), cleared as a polynomial \(F(Y)\) of degree at most six at normalized fifth clock \(Y=c_5/\gamma\), holds on **literal** rows 2–5. It is paid even if physical fifth is ordinarily silent. Its construction divides only the separated literal gap \(B_0-A_0\); the Vandermonde factors involving \(s\) are cleared. No premise about the invisible amplitude being nonzero is used.

* **Silent physical 5.** The actual affine reverse read at both rear pegs gives
  \[
  (x-z)\tfrac12(H_*(c)+H_*(d))=k(m-z)H_*(x).
  \]
  For \(H_*(m+\gamma v)=\sum h_jv^j\), put
  \[
  U=B^2h_0-ABh_2+A^2h_4,\qquad K=B(2B+A)H_*(x).
  \]
  These are the mean and terminal reads scaled by \(B^2\). At an actual candidate \(K\ne0\) from \(B\ne0,k\ne0,H_*(x)\ne0\). If \(K-U=0\), the comparison gives \((x-m)K=\gamma K=0\), impossible. Hence the true normalized fifth clock is \(Y=N/D\), where \(N=mK-xU\), \(D=\gamma(K-U)\). The necessary polynomial is \(D^6F(N/D)\) evaluated by homogenization. This uses the **actual** silent clock at physical fifth, neither a root of the ordinary nodal polynomial nor a choice of rear sign. The replay never inverts \(D\) in a residue algebra.

* **Silent physical 6 or 7.** Physical fifth is an ordinary missing node. Fold the star pair using \(B((X-m)^2-\gamma^2w)=B(X-m)^2+\gamma^2 A\). Using any two of the four moment rows, the signed cofactors are the true monic quadratic coefficient vector times their leading cofactor. This permits a zero leading cofactor and does not assume rank two. Evaluate the cofactor polynomial in \(X=\gamma Y\) and take its fixed-degree \((2,6)\) padded resultant with \(F(Y)\). All six row choices give zero. The physical fifth is a root of both; no second missing root or hypothetical clock is equated to the silent clock.

## Actual guards and complete local fibers

Guard removal is performed **over the exact characteristic-zero algebra** of each diagonal factor, before reduction. The regular scale is nonzero by the stated anchor chart. \(H_*(x)\ne0\) follows from the deflated ordinary read at the terminal. \(A+2B\ne0\) because \(A+2B=Bk\) with \(B,k\ne0\). For each known literal clock \(\xi=a,b\), \(B(\xi-m)^2+\gamma^2 A=B(\xi-c)(\xi-d)\ne0\) by distinctness of the nine actual sites. A removed factor of \(J_0\) has exact root support in the listed guard, checked by exact division; the replay does not delete any root merely because its residue hits a guard.

The exact guard plan is:

| Diagonal factor degree, exponent | Exact fourth support removed | Degree removed | Full reduced components |
|---|---|---:|---:|
| 257, 1 | None | 0 | 2 |
| 35, 2 | Regular scale | 2 | 4 |
| 2, 2 | Regular scale | 2 | 2 |
| 9, 2 | Regular scale | 2 | 4 |
| 27, 3 | Terminal amplitude | 3 | 4 |
| 4, 6 | Regular scale | 4 | 2 |
| 21, 25 | Rear-literal collision | 5 | 2 |
| 1, 27 | Rear-literal collision | 9 | 1 |
| 4, 27 | \(A+2B\) vanishes identically | Entire diagonal branch | 0 |
| 3, 33 | Rear-literal collision | 3 | 1 |

For speed, source-level CRT proposes a monic degree-\(r\) fourth factor \(D_0\) supported on each actual guard \(G\). It is accepted only when exact polynomial division checks \(D_0\mid J_0\) and \(D_0\mid G^r\) over the exact diagonal algebra. Neither CRT guesses nor a modular degree calculation can by themselves drop any factor.

Each surviving factor uses the complete monic diagonal reduction at \((1129,t=203)\). For each whole residue component, the exact guarded fourth polynomial is monic with \(p\)-integral coefficients, or at least one \(J_i\) retains its full stated \(s\)-degree with nonzero leading coefficient. This keeps a full monic model above that component. A characteristic-zero solution determines an embedding of \(\mathbb Q(t)\) via its actual orientation coefficient. The finite local model can use the prescribed place of that field with \(t\) reducing to \(203\), so testing this single residue orientation, with all diagonal components, does not assume the characteristic-zero sign. In each such algebra first intersect all four projected minors, then apply each of the two fifth-stage gates separately. A gcd of one certifies no common root for that placement. A genuine characteristic-zero solution would persist at a place of the finite integral local model, whereas the asserted reduced span is a unit. No claim about arbitrary reduction of an unknown tableau is made.

## Replay

Install `sympy==1.14.0` and `python-flint==0.9.0`, then run `python3 check_star567_regular_closed.py`. `--direct-integer` computes the exact integer Sylvester resultants directly instead of using CRT; `--independent-third` also verifies the optional third one. The [Lean structural receipt](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStarInteriorReads.lean) checks the actual mean-silent read, degree-six clearing identity, signed missing-node cofactor rule, and folded peg pair, separately from exact arithmetic and chronology. Checked on Lean/Mathlib 4.36.0. This is a scoped characteristic-zero result; neither other rear phases nor the unrestricted **10–11** stage interval is changed.
