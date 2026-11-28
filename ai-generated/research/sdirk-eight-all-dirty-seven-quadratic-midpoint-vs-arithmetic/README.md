# Both doubled endpoints preclude either prefix from starting D,D,D

Assume an all-dirty strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, exactly seven distinct clocks and genuinely quadratic singleton residual graph \(R\). D denotes a doubled clock label and S a singleton. **If both physical endpoints are D, neither actual opening triple can be D,D,D.** In particular each orientation has at least one literal singleton among its next two rows. This does not eliminate the remaining quadratic graphs or change the general 10–11 stage interval. No positivity or weight-sign premise is used.

## Scope and exhaustion

Orient the D,D,D prefix forward. The reverse starts D. If it is D,D,D, use the [two-triple-D exclusion](../sdirk-eight-all-dirty-seven-quadratic-two-triple-d/README.md); with exactly one later D use the [five-D boundary exclusion](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md). Otherwise it is D,S,S. Its literal star is [excluded separately](../sdirk-eight-all-dirty-seven-quadratic-triple-d-vs-star/README.md). In reverse arithmetic the [seven exact finite meshes](../sdirk-eight-all-dirty-seven-quadratic-triple-d-vs-arithmetic-finite/README.md) leave only distinct endpoints with actual forward midpoint arithmetic, addressed here. These are all actual first-three phases, with the reverse taken by genuine weighted mirror, not ad hoc chronological reversal.

## The only variable D,D,D mesh

Normalize to diagonal one, let \(\ell=1/\gamma=2m\), set \(h=m-1\ne0\), and use centered clock \(t=x-m\). The three D labels are \(-h,0,h\), and the actual forward clocks \(1,m,2m-1\) pay the normalized residuals \((1,\kappa,q)/2\), where
\[
 D(u)=-2+u+4u^2-u^3,\quad \kappa(u)=1+2u-u^2,\quad
 q_{\rm num}(u)=(1+4u-4u^2)D(u)+4u^2(3u-2),
\]
and \(\kappa=\kappa(h),q=q_{\rm num}(h)/D(h)\). In the centered convention use
\[
 L_4(t)=t^4-a t^2+b,\quad
 a=6m^2/7,\ b=3m^4/35,\quad L_3=t^3-c_3t,\ c_3=3m^2/5.
\]
Both endpoints are D, so the [odd projection](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) gives \(Q_0=Q/B=L_3-\mu t L_4\). Here \(\mu=(h^2-c_3)/L_4(h)\ne0\). Its actual factorization gives
\[
 Q_0=-\mu\, t(t^2-h^2)W(t),\qquad W(t)=t^2-S,\qquad
 S=\frac{(3/5)m^2h^2-(3/7)m^4}{h^2-(3/5)m^2}.
\]
No assumption \(S\ne0\) or \(S\ne h^2\) is made, so repeated graph roots and common \(P,W\) roots are kept.

Let \(T\) be the quadratic interpolating the actual \(g_{\rm f}=(1,\kappa,q)/2\) at \(-h,0,h\), and \(A_0\) interpolate \(L_4/g_{\rm f}\). The code checks \((A_0T-L_4)\bmod t(t^2-h^2)=0\). By the single known terminal overlap, with nonzero mirror conversion \(\lambda\),
\[
 B\lambda=\beta_0=-4L_4(h)/q,\qquad
 A_2=A_0-\beta_0T/\lambda.
\]
The actual guard denominators depending only on \(h\) are therefore \(m,h,\kappa,q,D(h),3h-2,L_4(h),h^2-c_3,L_4(\sqrt S)\). Here \(L_4(\sqrt S)=S^2-aS+b\) denotes a scalar polynomial evaluation in \(S\), not a real-root selection. Both Legendre denominators are nonzero by coprimality of \(Q_0,L_4\).

## True reverse arithmetic and normalized trace

Let \(v\ne0\) be the actual reverse arithmetic gap; its other two original clocks are \(s_2=h-v,s_3=h-2v\). Their residues in the reverse normalization are \(n_2/d_2=\kappa(v)/2\) and \(n_3/d_3=q_{\rm num}(v)/(2D(v))\). Thus the ratio gives \(q_{\rm num}(v)W(s_2)-\kappa(v)D(v)W(s_3)=0\). The exact identity
\[
 q_{\rm num}(v)W(s_2)-\kappa(v)D(v)W(s_3)
  =v\kappa(v)\,[D(v)(2h-3v)-(v-2)(3v-2)W(s_2)]
\]
uses the true first-three numerator. Cancelling only the literal nonzero \(v\kappa(v)\) gives the expression in brackets, a cubic in \(v\) over \(\mathbb Q(h)\). Leading coefficients may specialize to zero and are not guarded artificially.

Write \(R=rW\), so \(\nu=r/\lambda=\kappa(v)/(2W(s_2))\). The known two singleton zero conditions use the exact affine expansion
\[
 H=L_4+\beta_0\nu W T-\lambda\nu W(A_0+\beta_0\nu W)
\]
as in the finite packet. Each actual \(H(s_i)=0\) gives the augmented affine row
\[
 -n_i[d_i A_0(s_i)+\beta_0n_i]\lambda+
                        d_i^2L_4(s_i)+\beta_0 d_i n_i T(s_i)=0 .
\]
No division by an affine coefficient is needed.

The third affine row uses the correct [normalized quadratic trace](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md), \(2\sum1/g_i=\ell\sum b_i/g_i\). Concretely, define \(\mathcal R_4(f)\) as the coefficient of \(t^7\) of the remainder of \(H_3 f/Q_0\) modulo \(L_4^2\), with \(H_3=4m^6/175\). The unweighted inverse sum has scalar part \(-2(2S-a)/(r L_4(\sqrt S))\) and linear part
\[
 2\frac{(A_2\bmod W)_0}{L_4(\sqrt S)}
     +\sum_{d=0,\pm h}\frac{A_2(d)}{L_4(d)}.
\]
For \(S\ne0\) this is the two actual \(W\)-root sum after the logarithmic derivative. At \(S=0\) it holds unchanged: the negative derivative of \(H'/H\) at zero gives unweighted constant \(2a/(rL_4(0))\), and the linear term is \(2A_2(0)/L_4(0)\). Thus the rational trace specializes at the Hermite root without an inversion of \(W'\). The weighted inverse sum is \(\mathcal R_4(L_4/(rW)+A_2)\), valid by the signed algebraic residue calculation for any \(W\), including a repeated root. These formulas give \(c/r+\mathcal T(A_2)=0\), with \(\mathcal T\) linear and \(c\) scalar. Substitute the actual inverse scales and multiply by \(\lambda\kappa(v)\) to obtain
\[
 \kappa(v)\mathcal T(A_0)\lambda
                 +2cW(s_2)-\beta_0\kappa(v)\mathcal T(T)=0 .
\]

## Exact specialization-safe projection

The script constructs the three rows in \(\mathbb Q(h)[v]\) and their augmented \(2\times2\) minors. All are necessary even if every coefficient of \(\lambda\) vanishes. Before making integer polynomials, it audits the denominators of the symbolic trace inverses, its grade-two interpolation data, and the actual equations: every nonconstant denominator factor comes from the declared nonzero \(h\)-guards. It also removes only factors of true nonzero guards involving \(v,\kappa(v),D(v),q_{\rm num}(v),3v-2,W(s_i)\), or the distinct singleton-vs-doubled clock gaps \(s_i-d\). In particular no leading coefficient pivot in the \(v\) algebra is presumed invertible.

After clearing those denominators, take exact integer resultants in \(v\) of the cubic ratio and each of the three minors. Their degrees in \(h\) are \(74,66,96\). The gcd of the first two, after removing only roots of the allowed \(h\)-guards, is a unit. Thus there is no actual common \(h,v\) even when a specialized degree drops. The third resultant is independently replayed. This closes the final D,D,D boundary shape, including Hermite and signed-weight possibilities.

Run `python check_variable_midpoint.py` with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticMidpointVsArithmetic.lean) stages the exact scalar ratio identities; the full trace and integer-resultant exclusion is the source argument and replay, not end-to-end native Lean. No finite-characteristic transfer is used.
