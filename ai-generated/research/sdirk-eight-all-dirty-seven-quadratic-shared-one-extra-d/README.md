# Shared doubled endpoints cannot both use one later doubled clock in their boundary triples

Assume the all-dirty strict ten-stage SDIRK8 floor over a characteristic-zero field, with exactly seven distinct clock labels and genuinely quadratic singleton-residual graph \(R\). The two physical endpoints have the **same** D (doubled) clock label. This packet excludes the case when each actual first-three prefix has exactly one later D and one later S (singleton), irrespective of whether the two extra D labels match. It does not exclude one such prefix opposite D,S,S, and it does not change the numerical stage interval. All signed weights are allowed.

## Literal prefix pairs and graph shapes

With common diagonal normalized to one, shared endpoints force \(\ell=1/\gamma=2\) and centered \(t=x-1=0\) at both ends. The normalized first residual in either orientation is \(1/2\). The [odd projected quintic](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) has the form \(Q/B=L_3-\mu t L_4\), with nonzero \(\mu\), and \(L_4(t)=t^4-6t^2/7+3/35\). Let \(d\ne0\) be the actual forward extra D label, and \(e\) the other noncentral D label, with \(e\ne0,d\). The cubic \(P=t(t-d)(t-e)\) divides \(Q\). Write \(W\) monic quadratic and \(R=rW\), \(r\ne0\). The opposite-root support gives two complete shapes:
- If \(e=-d\) then \(W=t^2-S\) centered-even, with \(S=(21d^2-15)/(35d^2-21)\). This includes the repeated Hermite graph root \(S=0\) and allows \(S=d^2\), a common \(P,W\) root. The denominator is nonzero by \(\mu=(d^2-3/5)/L_4(d)\ne0\).
- If \(e\ne-d\), then the distinct squared labels give \(35d^2e^2-21(d^2+e^2)+15=0\). The five odd-quintic roots are \(0,\pm d,\pm e\), so \(W=(t+d)(t+e)\) is split. This is an exact field description; no real root or ordering is assumed.

At a noncentral D label \(y\), the three possible actual pair-data formulas within its own orientation are:

| Phase | Extra D residual \(g_D\) | Other S clock \(s\) | Its residual \(g_S\) |
|---|---|---|---|
| A2: second D in arithmetic | \(\kappa(y)/2\) | \(2y\) | \(q(y)/2\) |
| A3: third D in arithmetic | \(q(y/2)/2\) | \(y/2\) | \(\kappa(y/2)/2\) |
| S: either actual star order | \(\kappa(y)/2\) | \(2-y\) | \(\kappa(y)/2\) |

Here \(\kappa(u)=1+2u-u^2\), \(q=q_{\rm num}/D\) from the true arithmetic formula in the earlier packets. The star orders use the same unordered physical pair data because \(\kappa(2-y)=\kappa(y)\); no permutation of a tableau is asserted. All literal guards \(u\ne0\), nonzero residues, arithmetic \(D,3u-2\ne0\), and the star's distinct-clock conditions are applied. Arithmetic \(u=2\) is also forbidden with shared endpoints by the [first-departure argument](../sdirk-eight-all-dirty-seven-quadratic-shared-split-arithmetic/README.md): any departure from the first residual would have to occur only at the terminal, giving at most two levels in contradiction to pure paid moments.

Let \(\lambda\ne0\) convert genuine reverse residuals to original normalized residuals. The two *different physical pairs* at clock 0 force \(\lambda\ne1\) and, by Vieta, \(B\lambda=\beta=-4L_4(0)\). A singleton in original coordinates is not at a graph zero or a D label. Its \(H=0\) equation is \(C=L_4/g\) for \(C=A_2+B R\). No division by \(W\) is made at a doubled label in any of the following checks.

## Matching extra D labels

The reverse extra D in original coordinates equals \(d\), so its own normalized D coordinate is \(-d\). The two known residual products at 0 and \(d\) give
\[
                       L_4(d)=4 L_4(0)g_{\rm f,D}(d)g_{\rm r,D}(-d).
\]
All unordered phase pairs suffice after genuine reflection. A2/A2 or A3/A3 would repeat a supposed singleton clock at both ends, impossible. The remaining four pairs project to the following exact irreducible polynomials after removing only actual nonzero phase guards:
\[
 \begin{array}{c|l}
 \mathrm{A2/A3}& p(d)=8d^5+64d^4-44d^3-146d^2+45d+60\\
 \mathrm{A2/S}&8d^2-3\\
 \mathrm{A3/S}&-p(-d)\\
 \mathrm{S/S}&8d^2-3 .
 \end{array}
\]
For each exact field the replay keeps the centered-even case (with a branch for Hermite \(S=0\)), and both possible split third D labels, adjoining \(\sqrt S\) only where needed. The required \(Q/B=-\mu P W\) is checked in every tower, including the possibility of a shared graph/D root. In these projected fields there happen to be four even and eight split placements, with no Hermite specialization.

The known original forward singleton fixes \(r=g_{\rm f,S}/W(s_{\rm f})\); the other fixes \(\lambda=r W(s_{\rm r})/g_{\rm r,S}\) where \(s_{\rm r}\) is reflected back to the original clock. If any such denominator vanishes, its actual singleton residual cannot be nonzero. Thus \(B=\beta/\lambda\). At the two observed D labels, the actual two-root sums give
\[
 C(0)=-B(1+\lambda)/2+B R(0),\qquad
 C(d)=-B(g_{\rm f,D}+\lambda g_{\rm r,D})+B R(d).
\]
With \(C(s_{\rm f})=L_4(s_{\rm f})/g_{\rm f,S}\), these determine the degree-two polynomial \(C\). The other observed singleton demands \(C(s_{\rm r})=L_4(s_{\rm r})/(\lambda g_{\rm r,S})\). All twelve exact placements fail that fourth value. The equality test checks both split roots, not only a base-field square root.

## Distinct extra D labels

Now the forward extra D is \(d\), and the reverse extra D in original coordinates is \(e\), so its own normalized input is \(-e\). There is still one actual overlap at 0 and \(B\lambda=\beta=-4L_4(0)\). The known singleton residues and their graph values fix \(r,\lambda,B\) as in the matching proof. The three distinct D labels instead give
\[
 \begin{split}
 A_2(0)&=-B(1+\lambda)/2,\\
 A_2(d)&=L_4(d)/g_{\rm f,D}-B g_{\rm f,D},\\
 A_2(e)&=L_4(e)/(\lambda g_{\rm r,D})-B\lambda g_{\rm r,D}.
 \end{split}
\]
These fix the actual quadratic \(A_2\) and hence \(C=A_2+B R\). The two observed singleton equations \(L_4(s)-g C(s)=0\) are necessary. There is no unproved invertibility assumption: the interpolation denominators are differences of three proven distinct D labels, and all other denominator factors are checked against the actual nonzero guards.

**Centered-even (including Hermite).** Here \(e=-d\) so the reverse's own D coordinate is the same \(d\) as forward. If both phase pair-data formulas agree, their same residue value at the two reflected S sites against even \(W\) forces \(\lambda=1\), duplicating the physical terminal pair. For the three remaining pairs compute the two singleton equations in \(\mathbb Q(d)\). Their numerator gcd degrees before guards are \(3,0,0\) for A2/A3, A2/S, and A3/S respectively, and all guarded gcds are units. \(S=0\) does not produce any division or rank assumption, nor does \(S=d^2\).

**Split.** Here \(e\ne-d\), retain \(d,e\) as variables and \(W=(t+d)(t+e)\). The two singleton equations give exact integer-polynomial numerators after clearing only the verified guard denominators. For each of six unordered phase pairs, take resultants of these numerators with \(35d^2e^2-21(d^2+e^2)+15\) in \(e\). In every case their gcd is a unit after removing only univariate factors of actual nonzero guards in \(d\). No degree-drop or finite-field reconstruction is needed because the elimination is polynomial before any specialization. There is no assumption that the split roots or any S clocks are ordered.

These computations use the two literal known S reads and do not require the normalized trace. They also do not divide by a rank coefficient to discard possible singular fits.

## Replay

Run `python shared_match_d.py`, `python shared_opposite_even_d.py` and `python shared_distinct_split_d.py` with SymPy 1.14 and python-flint 0.8. All use exact arithmetic; the same-directory pair helper is imported from the first file. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSharedOneExtraD.lean) checks small scalar fit identities on Lean/Mathlib 4.36.0; no end-to-end theorem is asserted. No finite-characteristic conclusion is made.
