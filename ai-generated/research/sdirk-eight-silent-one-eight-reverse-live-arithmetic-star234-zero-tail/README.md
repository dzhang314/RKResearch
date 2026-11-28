# Arithmetic front, star rear, zero centered tail, literal silent placement

Consider a strict ten-stage SDIRK8 tableau in the [constant nonzero nine-site reverse-numerator chart](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) over a characteristic-zero field. Physical first is the sole nonzero quadratic-defect stage and ordinarily silent; eight ordinary active clocks are distinct; the other ordinarily silent stage has nonzero actual reverse read at a distinct ninth clock. Here the literal front is arithmetic, the ordinary rear is star (so physical eighth is ordinary), the genuine mixed quintic has regular fourth anchoring, and the centered star tail \(A+Bv^2=0\) has \(A=B=0\). This packet excludes all three extra silent **literal physical 2, 3, or 4** placements. The interior physical 5–7 packets are separate, and the unrestricted **10–11** bound is unchanged.

The [arithmetic-front zero-tail model](../sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-zero-tail/README.md) gives the same homogeneous profile
\[
 H_g=-8P L_3+(162\gamma-45)Q L_4+5Q L_5
\]
and the full degree-eight diagonal from true literal amplitude agreement, with \(Q,P\) as in the [zero-tail identities](../sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail/README.md). These literal values remain correct even when one literal is ordinarily silent. The true normalization is \(H=H_a H_g/H_g(\gamma A_0)\); its denominator is nonzero by the actual nonzero \(H_a\). At the actual fourth the known literal profile equation \(H(\gamma s)=H_4(s)\) holds regardless of weight. Factoring exact padded roots \(s=A_0,B_0\) is lawful because all three literal clocks belong to nine distinct *reverse* sites (exactly one of them is silent ordinary). The remaining fourth equation has full degree three.

Put \(a=\gamma A_0,b=\gamma B_0,q=\gamma s,x=1-\gamma,m=1-2\gamma\), with ordinary rear clocks \(c,d=m\pm\gamma v\). The actual extra silent reverse clock is the correct literal \(z=a,b,q\) for physical \(2,3,4\), respectively. Its two actual tail comparisons imply
\[
 (x-z)\tfrac12(H(c)+H(d))=(2-w)(m-z)H(x),\qquad w=v^2 .
\]
Writing \(H(m+\gamma U)=\sum h_jU^j\), this gives the quadratic
\[
 (x-z)(h_0+h_2 w+h_4 w^2)-(2-w)(m-z)H(x)=0 .
\]
Its leading coefficient is genuinely nonzero because \(x\ne z\) and \(h_4=-h_5\ne0\) in the identically zero centered quintic. Choose the correct five ordinary pegs by omitting the actual silent literal from \(a,b,q\), retaining \(x\), and appending both ordinary \(c,d\). The unordered pair supplies factor \((X-m)^2-\gamma^2w\). In each case the ordinary nodal polynomial has a monic missing cubic above these five pegs. Its four paid nonconstant Bézout coefficient rows give one required \(4\times4\) determinant. Only ordinary precision **seven** is used; no fifth-stage condition or orientation interchange is used.

At \(p=1129,t=203\) the full degree-eight diagonal keeps both components of degrees 1 and 7. All literal normalization and fourth-cubic leading coefficients are units. For each diagonal component and each actual placement, retain the complete monic fourth cubic and the complete monic gap quadratic. The corresponding five-peg determinant is a unit in all six full algebras. This checks all roots, rather than extracting a preferred rear square root. A characteristic-zero candidate embeds \(\mathbb Q(t)\) and would persist at this residue place of the monic local model. No unknown weights or ordering enter the argument.

Install `sympy==1.14.0` and `python-flint==0.9.0` and run `python3 check_arithmetic_star234_zero_tail.py` from this directory. The [centered zero-tail coefficient identities](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStar4ZeroTail.lean) and [actual mean read](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStarInteriorReads.lean) are reusable native gates, previously checked on Lean/Mathlib 4.36.0. This new local arithmetic is exact source-level.
