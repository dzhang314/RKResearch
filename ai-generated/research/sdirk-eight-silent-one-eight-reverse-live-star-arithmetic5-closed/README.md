# True ordinarily silent fifth, regular star front and ordinary arithmetic rear

This is the actual silent-fifth companion to the [silent-sixth/seventh closure](../sdirk-eight-silent-one-eight-reverse-live-star-arithmetic67-closed/README.md). The scope is strict ten-stage SDIRK8 over **every characteristic-zero field**, with physical first the sole nonzero quadratic-defect row and ordinarily silent. Exactly eight ordinary active clocks are distinct. The other ordinarily silent physical row is **fifth** and has an actual nonzero reverse read at a ninth distinct clock. The reverse numerator is constant nonzero. The profile is a genuine mixed quintic with both early quartic anchors and the regular fourth anchor nonzero. The front is star, the ordinarily weighted rear is arithmetic. Literal silent 2–4, an arithmetic front, and the unrestricted **10–11** interval remain separate.

## Genuine actual fifth, not a missing ordinary root

Write \(x=1-\gamma\), \(c=x-\gamma u\), \(d=x-2\gamma u\) for physical 10, 9 and 8, and \(k=1+2u-u^2\). Here \(\gamma,u,k,H(x)\ne0\). The four true fixed ordinary pegs and the [actual double-gap projection](../sdirk-eight-silent-one-eight-reverse-live-star-arithmetic67-closed/README.md#independent-true-tail-and-ordinary-fifth) give the same two rational fourth equations \(A_*(\gamma,s)=B_*(\gamma,s)=0\), with \((s,\gamma)\)-degrees \((48,132),(54,156)\). This uses the actual rear \(N(u)=N(2u)=0\) and paid tail \(F(u)=0\), but **does not** yet use a fifth condition. The ordinary moment precision remains **seven**. In particular the true nodal \(N\) has degree four and its leading coefficient \(R_4\ne0\) by the known-peg pivot. Its true second synthetic remainder \(D_1(u)\) is zero without a residue distinctness assumption.

The actual silent clock \(z\) is determined by \((x-z)H(c)=k(c-z)H(x)\). The denominator \(H(c)-kH(x)\) is nonzero, since its vanishing would imply \(x=c\). Let
\[
 L=\frac{H(c)-kH(x)}{u}.
\]
The numerator is exactly divisible by \(u\) as a polynomial, so \(L\) has degree four in \(u\), and \(L\ne0\) at the true tableau. Then actual normalized fifth \(Y=c_5/\gamma\) is
\[
 Y=\frac{xL+\gamma kH(x)}{\gamma L}.
\]
This uses the actual fifth amplitude from \(H\), and no claim that this clock is in the ordinary nodal support. The [previous literal fifth determinant](../sdirk-eight-silent-one-eight-reverse-live-star567-regular-closed/README.md#two-distinct-actual-fifth-stage-gates) is paid on actual rows 2–5 even when fifth is ordinarily silent. Its cleared cubic \(G_5(Y)\) after the known literal padding therefore gives
\[
 (\gamma L)^3 G_5\!\left(\frac{xL+\gamma kH(x)}{\gamma L}\right)=0 .
\]
The replay uses its polynomial numerator and never inverts \(L\) after reduction. The raw degree in \((u,s,\gamma)\) is \((12,12,45)\); removing only \(\gamma^2\) gives the actual silent-fifth equation \(G_{\rm silent}\) of degrees \((12,12,43)\). The same equation is independent of any ordinary fifth quartic root.

## Full characteristic-zero projection and its exact cover

Form \(\operatorname{Res}_s(A_*,B_*)\) over the rationals with integer primitive inputs. Its cap and exact degree are **14616**, and its exact strict-diagonal valuation is **1953**. To reconstruct the integer polynomial, each modular image preserves the full preliminary input \(s\)-degrees. The determinant coefficient bound is the product of the row \(\ell^1\) norms, with 41273 bits. The 688 prime CRT product exceeds twice that bound, so the signed reconstruction is exact. Both a whole first prime image and the independent whole image at 65537 agree with the original interpolation. After dividing the true nonzero strict \(\gamma\)-power and content, the projection is an exact nonzero degree-12663 polynomial.

The exact leading-\(s\) common projection and the two smaller exact guard resultants \(\operatorname{Res}_s(A_*,H(x))\), \(\operatorname{Res}_s(A_*,R_4)\) (using their normalized legitimate representatives) propose eleven exact small factors. These auxiliary proposed factors are **not** imposed as extra actual equations: full exact product division checks their powers as a cover of the actual projection together with the resulting degree-4923 quotient. Every actual \(\gamma\) is in one of these exact components. The auxiliary resultant degrees and strict-diagonal valuations are \(924,159\) and \(1884,222\).

In the eleven small components specialize a fourth equation over the entire monic characteristic-zero diagonal algebra, allowing exact fourth-degree drops. Use its checked monic normalization, and when required keep the exact quotient by a proposed monic factor \(D\) of the fourth equation. The accepted \(D\) also divides a power of the true nonzero \(R_4\) or \(H(x)\). Both identities are checked over the exact diagonal algebra, not inferred from a modular leading failure. In every one of the **39** complete local diagonal components at \(65537\), the entire resulting monic fourth basis is coprime to the two true fourth equations. This retains all unknown fourths, including those not forbidden by the source guard before reduction.

For the degree-4923 quotient there are **12** complete local diagonal components at that same place. A full fourth projection supplies a leading unit. Every remaining fourth component has the full missing quartic \(N\) with a checked leading unit. Its entire monic algebra has no root common to \(D_1,F,G_{\rm silent}\). Thus no actual tail can occur even if its two true ordinary root reductions merge. The clock arguments only require the algebraic subfield generated by the candidates in these monic bases; no integrality assumption on the unknown strict tableau is used. No artificial \(u-1\) or \(u-2\) divisors are removed.

## Replay and native scope

Install **sympy==1.14.0** and **python-flint==0.9.0** and run **python3 check_star_arithmetic5.py** with the declared sibling directories. The optional geometric-grid interpolation is for a tested LP64 FLINT 3.6.0 wheel. At each prime the actual points \(1,r^2,\ldots,r^{2d}\) are pairwise distinct, checked by the order of \(r^2\). Each point evaluates the same padded Sylvester determinant. If both univariate degrees drop, the determinant is zero because of the common projective infinity root. If only one degree drops, the leading power of the other and the signed degree correction follow from the resultant root-product formula. Thus no point is removed from the geometric interpolation. The default is serial; set **RK_CRT_WORKERS=3** for three local arithmetic workers where memory permits. The ordinary backend is available without a C compiler or with **RK_DISABLE_FAST_CRT=1**.

The [previous native Lean scalar lemmas](../../lean/RKCert/ReviewedNative/SDIRK8OrdinaryArithmeticRearQuartic.lean) check the actual affine denominator and second synthetic remainder on Lean/Mathlib 4.36.0. The newly specialized silent-fifth arithmetic projection and complete local verification are exact source-level certificates.
