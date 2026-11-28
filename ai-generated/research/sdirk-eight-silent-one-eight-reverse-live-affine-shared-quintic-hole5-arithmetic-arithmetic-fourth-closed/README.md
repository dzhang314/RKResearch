# Regular corrected ordinary hole5, arithmetic front and ordinary arithmetic rear, true silent fourth

This excludes the regular arithmetic-front, ordinarily weighted arithmetic-rear case with extra ordinarily silent but reverse-live **physical stage 4**. It is the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) for ten strict SDIRK8 stages over characteristic-zero fields. First alone has nonzero quadratic defect and is ordinarily and reversely silent. The eight ordinary clocks are distinct; the reverse-live fourth is a ninth site. The common affine/quintic root \(r\) is the ordinary fifth, with actual amplitude \(h_5=0\), continued \(H(r)\ne0\), and early rank two \(\Delta\ne0\). No ordering is used.

Write \(z=c_4=\gamma s,\ Y=r/\gamma,\ a=c_2,b=c_3,\ H_N=\Delta H=\alpha_N L_4+\beta_N K_3\). Though ordinarily silent, the actual fourth has the true cubic amplitude \(H_N(\gamma s)=\Delta H_4(s)\) and is not the hole. The [literal arithmetic front](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-star-literal-closed/README.md) gives \(J(\gamma,Y,s)=\Psi(s,Y)=0\) from that true fourth and the actual zero fifth, with only the two true fourth pads and no artificial fifth pad. Their exact padded \(s\)-resultant divided by \(\gamma^3\ne0\) is \(P(\gamma,Y)\) of bidegree \((17,27)\) in \((Y,\gamma)\).

## Actual arithmetic rear at \(z=\gamma s\)

Set \(x=1-\gamma,\ c=x-\gamma u,\ d=x-2\gamma u,\ k=1+2u-u^2\). The actual rear law in the [arithmetic literal companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-arithmetic-literal-closed/README.md) gives quintic \(F(u)=0\) by exact division by \(u^2\). The penultimate comparison gives
\[
 G_0+sG_1=0,\qquad
 G_0=\frac{xH_N(c)-kcH_N(x)}u,\qquad
 G_1=\frac{\gamma(kH_N(x)-H_N(c))}u .
\]
Its only polynomial gap division is \(u\ne0\). The actual \(G_1\ne0\): if it were zero the equation would force \(G_0=0\), hence \(H_N(c)=kH_N(x)\) and \(kH_N(x)(x-c)=0\), contrary to the true factors. We do **not** invert \(G_1\) in the exact projections.

The homogeneous quadratic/linear projection \(C=J_2G_0^2-J_1G_0G_1+J_0G_1^2=0\) works at every nominal degree loss. In \((Y,u,\gamma)\) it has degrees \((9,6,32)\). Divide only \(\gamma^2\) to obtain \((9,6,30)\). The exact padded resultant with quintic \(F\) in \(u\) has \((Y,\gamma)\)-bidegree \((63,210)\). Divide only \(\gamma^{16}\alpha_N^2\) to get \(Q\) of \((57,182)\); \(\alpha_N\ne0\) follows from actual quartic degree.

The exact padded \(Y\)-resultant of \(P,Q\) has diagonal degree 3949. Divide only \(\gamma^{624}\beta_N^{171}\), retaining the full monic degree **2641** over \(\mathbb Q(t)\), \(2t^2=1\). The factor \(\beta_N=\Delta b_rH(r)\ne0\) is true by the rank and correction hypotheses. The rational norms of the two nominal \(Y\)-leading coefficients and retained diagonal have gcd one, so a simultaneous nominal leading drop is not discarded by a modular convention. Every exact guard quotient is checked by coefficient shift or polynomial division.

## Full finite fibers and actual ordinary pegs

The true five known ordinary nonhole pegs are \(a,b,d,c,x\), **not** actual \(z=\gamma s\). Their \(E_5\) gives \(D_7=E_5R_2\) for the monic quadratic with true ordinary roots 6 and 7. The [signed coefficient and terminal rows](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs) use \(\Lambda=H_N(r)I-\beta_N\mathrm{ev}_r\) and actual \(b_9=b_{10}\). All four minors must vanish without a mass or Cramer pivot.

At \((1129,t=203)\) retain all degree-preserving monic diagonal factors with their multiplicities, the full \(Y\)-gcd with a checked full leading unit in at least one defining polynomial, and the full \(u\)-law \(F\) or its necessary gcd with \(C\) when its Euclidean pivots are units. In \(s\) keep all three physical conditions \(J,\Psi,G_0+sG_1\), using a full monic defining polynomial whenever a Euclidean pivot is nonunit. Retain the actual penultimate comparison at \(z=\gamma s\) and all four signed/terminal minors. The residuals generate a unit in all **14** complete components, with six already inconsistent in \(s\). This proof uses finite localization, not good reduction of an unknown tableau.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_arithmetic_fourth.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and declared sibling proofs. The optional LP64 FLINT 3.6.0 geometric grid kernel is inherited from the [previous verified exact backend](../sdirk-eight-silent-one-eight-reverse-live-star-arithmetic5-closed/README.md). At each split prime separately use both images \(2t=\pm\sqrt2\), recombine in the basis \(1,\sqrt2\), and reconstruct once the product exceeds twice the certified integral coefficient bound. The independent standard resultant checks all coefficients at the first prime and again at 65537. Nominal degrees and one-/two-sided degree-drop corrections are the same padded Sylvester determinant, not numerical interpolation. The source has the ordinary exact FLINT fallback when the geometric backend is unavailable; it is slower. The [native actual affine pivot lemma](scalar-draft.lean) is supplied as a separate Lean candidate; native startup timed out during this replay window, so only the exact source-level certificate is checked here.

Together with the [ordinary star-rear fourth](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-star-fourth-closed/README.md), this closes actual silent fourth in both ordinary rear phases of the regular arithmetic front. Later silent rows and other ordinary holes are separate. The unrestricted **10–11** interval is unchanged.

The publication replay independently reproduced the complete exact arithmetic. Any accompanying Lean scalar source is a draft, not a kernel-checked proof of this result.
