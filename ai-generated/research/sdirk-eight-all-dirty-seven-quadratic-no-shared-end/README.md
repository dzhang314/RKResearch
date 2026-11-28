# Exactly seven all-dirty clocks cannot share their two physical endpoint labels

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, every quadratic residual nonzero, and exactly seven distinct physical clock labels. Then the two actual endpoint labels are **different**, so the original common diagonal is **not \(1/2\)**. This is a necessary condition, not a ten-stage nonexistence claim or a change to the general 10–11 stage interval. Signed weights are allowed.

## Exact case exhaustion

The [constant](../sdirk-eight-all-dirty-seven-constant/README.md) and [affine](../sdirk-eight-all-dirty-seven-affine-final/README.md) cases are already excluded, so \(R\) is genuinely quadratic. If the two endpoint labels were shared, that clock would be D (doubled) because the first and last are different physical rows. The [no D,D,D at either end](../sdirk-eight-all-dirty-seven-quadratic-midpoint-vs-arithmetic/README.md) theorem covers both shared and distinct D endpoints. So the two other labels in each opening together include at least one singleton (S). There are then three possibilities:
1. Both have two later singleton labels. Use the [quadratic star / centered-even exclusions](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) and the [shared split arithmetic exclusion](../sdirk-eight-all-dirty-seven-quadratic-shared-split-arithmetic/README.md).
2. Both have exactly one later D. Use the [matching and nonmatching shared endpoint exclusions](../sdirk-eight-all-dirty-seven-quadratic-shared-one-extra-d/README.md).
3. One has exactly one later D and the other has two later S. Orient the one-later-D prefix forward. If the reverse D,S,S is star, use the [shared mixed-star exclusion](../sdirk-eight-all-dirty-seven-quadratic-shared-mixed-star/README.md). The literal reverse arithmetic is the final case proved below.

These are physical prefix shapes, and the orientation uses the true weighted mirror of the saturated order-eight tableau. The result \(\gamma\ne1/2\) follows because the complete normalized endpoint clocks are \(1,\ell-1\) with \(\ell=1/\gamma\).

## The final mixed arithmetic graph

Scale the common diagonal to one. Shared endpoints give centered clock \(t=x-1=0\) at both ends and \(\ell=2\). Let \(d\ne0\) be the one later forward D label, \(e\) the other D label, and write \(R=rW\) with \(W\) monic quadratic. The [odd projection and paired squared-root relation](../sdirk-eight-all-dirty-seven-quadratic-shared-one-extra-d/README.md) give two exact possibilities:
- Centered-even: \(e=-d,\ W=t^2-S,\ S=(21d^2-15)/(35d^2-21)\), including \(S=0\) or \(S=d^2\).
- Split: \(e\ne-d\) and \(W=(t+d)(t+e)\), with
\[
 \Theta=35d^2e^2-21(d^2+e^2)+15=0.
\]
Both follow by factoring \(Q/B\) by the D polynomial, not by presuming simple graph roots.

Use the earlier literal forward A2, A3 and S pair data: for its extra doubled label \(d\), let \(g_D\) be the known residue there, and let \(\sigma,g_f\) be the forward singleton label and residue. Their nonzero guards, including \(W(\sigma)\ne0\), give \(r=g_f/W(\sigma)\). Write \(\beta=B\lambda=-4L_4(0)\) by the actual residual product at the shared endpoint, where \(\lambda\) is the nonzero reverse-to-original residual scale. In particular \(\lambda\ne1\), since the two endpoint pairs must differ in residue at their shared clock.

For actual reverse arithmetic gap \(v\), the two other original singleton coordinates are \(s_2=-v,s_3=-2v\). Use \(\kappa(v)=1+2v-v^2\), \(D(v)=-2+v+4v^2-v^3\) and put \(\widehat q=D(v)-v(v-2)(3v-2)\). The true third residue numerator is \(\kappa(v)\widehat q\). Write \(W(t)=t^2+b t+c\). The actual singleton ratio gives
\[
 \widehat R(v)=D(v)(b-3v)-(v-2)(3v-2)W(-v)=0.
\]
Indeed \(W(-v)-W(-2v)=v(b-3v)\); multiplying the displayed gate by \(v\kappa(v)\) gives the exact paid ratio numerator \(q_{\rm num}(v)W(-v)-\kappa(v)D(v)W(-2v)\). The cancelled factors \(v,\kappa(v)\) are actual nonzero guards. The equation stays polynomial even if its leading coefficient specializes to zero.

The first reverse S value gives \(\mu_v=\kappa(v)\lambda=2rW(-v)\). Put \(C=A_2+B R\), and let \(C_*=\kappa(v)\lambda C\). The actual D values and forward S value give
\[
 \begin{split}
 C_*(0)&=-\tfrac{\beta}{2}[\kappa(v)+\mu_v]+\beta r\kappa(v) W(0),\\
 C_*(d)&=\mu_v L_4(d)/g_D-\beta\kappa(v)g_D+\beta r\kappa(v) W(d),\\
 C_*(\sigma)&=\mu_v L_4(\sigma)/g_f .
 \end{split}
\]
The first follows from the two actual residuals \(1/2,\lambda/2\) of \(U\) at clock zero, the second from the actual forward \(U=0\) at \(d\), and the last from \(H=0\) at the forward singleton. The three clocks are different, so these values determine the quadratic exactly. The two actual reverse singleton equations become
\[
 2L_4(-v)-C_*(-v)=0,\qquad
 2D(v)L_4(-2v)-\widehat q\, C_*(-2v)=0 .
\]
These identities retain all \(W\) roots (even repeated or common with \(P\)); none divide by \(W\) at a D label. No normalized trace is needed.

## Specialization-safe exact projections and actual Hermite fibre

The script clears the genuine denominator guards in the interpolation and the preceding equations, verifying each denominator factor. It removes polynomial factors only for true nonzero conditions such as distinct S/D labels, true phase denominators and nonzero \(W\) values on singleton rows. Arithmetic \(u=2\) or \(v=2\) are guarded by the [shared-clock first-departure exclusion](../sdirk-eight-all-dirty-seven-quadratic-shared-split-arithmetic/README.md). The guard \(\mu_v-\kappa(v)\ne0\) says \(\lambda\ne1\) and does not presume a generic \(\lambda\).

Take exact integer resultants in \(v\) of each pair among the ratio and the two singleton equations. In the split case further eliminate \(e\) with \(\Theta\) **separately for each projection**. Only then take the univariate gcd in \(d\), stripping known true \(d\)-only guard factors. This order does not infer anything from a bivariate gcd about isolated common roots. The exact projected degree triples and guards yield:

| Graph shape | Forward phase | Degrees of three resultants in \(d\) | Guarded gcd |
|---|---|---|---|
| Even | A2 | 22, 33, 50 | unit |
| Even | A3 | 31, 42, 74 | unit |
| Even | S | 13, 24, 26 | \(7d^2-5\) |
| Split | A2 | 44, 66, 100 | unit |
| Split | A3 | 62, 78, 124 | unit |
| Split | S | 26, 48, 52 | unit |

The even-star residual projection is a **genuine Hermite specialization**: \(S=0\) and \(W=t^2\). It is not discarded. At this exact quadratic field specialize all three integer equations and take their gcd in \(v\); it is exactly \(v\) up to scalar, forbidden. This covers any loss of degree in that fibre. Hence the last possible shared-clock chronology fails.

Run `python check_shared_mixed_arithmetic.py` with SymPy 1.14 and python-flint 0.8. It imports the sibling `prefix_scalars.py`. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticNoSharedEnd.lean) checks the scalar true ratio numerator and the cleared reverse singleton factor on Lean/Mathlib 4.36.0; no end-to-end Lean theorem is claimed. All field conclusions here are characteristic zero.
