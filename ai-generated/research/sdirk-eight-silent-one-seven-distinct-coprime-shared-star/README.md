# Coprime shared literal balance with active star eighth

Use the [detected seven-distinct active strict SDIRK8 chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at ten stages over a characteristic-zero field. The only nonzero quadratic residual is at individually weight-zero physical first, \(k\ne0\), and \(Q\) is affine nonconstant coprime to \(L_4\). Exactly one literal front is active. The silent literal shares its actual clock \(z\) with one other physically silent stage and their reverse aggregate is nonzero, separate from every active site. That second silent is physical six or seven here, so fourth and fifth are active and eighth is active with its star geometry. Neither actual silent amplitude is set to a weighted virtual value. The separate [silent-fifth](../sdirk-eight-silent-one-seven-distinct-coprime-shared-fifth/README.md) and [silent-eighth](../sdirk-eight-silent-one-seven-distinct-coprime-shared-eighth/README.md) packets use different physical chronology.

## Center the actual tail

With \(N=A-\gamma I,\ M=CA-AC-A^2\) write \(\boldsymbol h=N\boldsymbol g,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\). Denote normalized literal clocks \(a,b\) (active and silent), so \(z=\gamma b\). Put \(x=1-\gamma,\ m=x-\gamma,\ v=u-1,\ V=v^2\); the actual active clocks are \(c=m-\gamma v,\ d=m+\gamma v\) and \(k=2-V\), with \(v\ne0,\ V\ne1,2\). At active sites the reverse ratio \(w_i/b_i\) is proportional to \(L_4(c_i)/(q(c_i)(c_i-z))\). Set
\[
 T=k L_4(x)(c-z)(d-z),\quad
 S=(x-z)\bigl[L_4(c)(d-z)+L_4(d)(c-z)\bigr].
\]
They are symmetric in \(c,d\). The sum of the two actual star-tail comparisons gives, up to common nonzero scale, \(q(x)=2\gamma T,\ q'=2T-S\). Their difference gives
\[
 v(2T-S)=(x-z)\bigl[L_4(d)(c-z)-L_4(c)(d-z)\bigr].
\]
After removing the exact odd factor \(v\) from the difference and exact padding \(V-1\) for a forbidden tail collision, the condition is \(\alpha(\gamma)+\beta(\gamma)V=0\). Both exact coefficient degrees are six. The exact gcd of \(\alpha,\beta\) after the necessary nonzero diagonal, terminal, and active literal guards is one, so \(\beta\ne0\) in any actual method. Homogeneous substitution of \(V=-\alpha/\beta\) is therefore legitimate.

## Fifth ordinary peg is the actual fourth

Use the [scalar nodal identity](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) \(L_4 W_D-DW_{L_4}=\kappa q^2\), with \(D\) the monic degree-seven active nodal polynomial. It implies that \(D\) is \(L_4\) times a cubic minus a nonzero multiple of \(V_q=q^2 W_{L_4}^{-1}\bmod L_4\). At the five actual ordinary pegs \(\gamma a,x,c,d,\gamma s\) (actual fourth \(s\)), the scalar evaluation determinant of \(L_4,XL_4,X^2L_4,X^3L_4,V_q\) is zero. After the nonzero Vandermonde is removed by exact Newton divided differences, it is a polynomial \(D_5\) of degree at most three in \(s\), and symmetric in \(c,d\).

On the active profile the normalized \(h\) is \(P(Y)/Q_0(Y)\), with \(P(Y)=h_aq(\gamma a)L_4(\gamma Y)\), \(Q_0(Y)=L_4(\gamma a)q(\gamma Y)\). Actual fourth satisfies the padded polynomial \(\Phi=(Q_0H_4-P)/(Y-a)\). Both fourth polynomials are symmetric. Homogenize the substitution for \(V\) and take the exact resultant of \(\Phi,D_5\) in \(s\), with its genuine distinct-node, nonzero diagonal/profile readings, and coprime pole guards. Its guarded diagonal degree is 51 for each front orientation. The sign of the actual \(v\) is never chosen; both orientations satisfy the same symmetric conditions.

## Signed masked actual fifth test

Split the exact leading degree of \(\Phi\). In each reduced diagonal factor impose **both** \(\Phi,D_5\) using their complete gcd. The four known ordinary pegs have the explicitly symmetric mask
\[
 (Y-\gamma a)(Y-x)\bigl[(Y-m)^2-\gamma^2 V\bigr].
\]
Use the [paid rational moments through degree nine](../sdirk-eight-silent-one-seven-distinct-anchors/README.md), \(f\mapsto\sum b_i f(c_i)/(c_i-\xi)^2\) at the physical pole \(\xi=-q(0)/q'\). The six masked moments give the cleared three-missing-site cubic containing actual fourth. For actual fifth, add fourth to the mask: exactly two ordinary sites remain, giving the rank-two \(3\times3\) signed Hankel condition and a cleared two-missing-site quadratic. The two exact literal fifth pure reads at the active profile have earlier factors \(y-a,y-s\); actual active fifth cannot equal either. Their resultants with the signed quadratic, their own resultant, the actual fourth missing-cubic read, and the signed Hankel condition jointly generate the unit ideal. No pivot of an unknown moment determinant is inverted and no particular orientation of \(v\) is substituted.

## Verification

Run `python3 check_coprime_shared_star.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the sibling repository proof tree. The runner lists the finite six-clock, literal-pole and later helper paths (including the exact quadratic-coefficient guard routines). All 4 complete orientations use \((1103,t-161)\) for the finite checks after exact guarded projections and leading-degree splits. All irreducible reduced components and full fourth gcds are retained. The local-unit lift does not assume reduction of the actual tableau. The [Lean lemma](../../lean/RKCert/ReviewedNative/SDIRK8CenteredStarRead.lean) kernel-checks the actual star sum/difference step on Lean/Mathlib 4.36.0. Saturation, projection, and masked arithmetic remain source-level.

This does not address the active **arithmetic** eighth with a shared silent six or seven, the nonliteral balances, or the no-active-literal coprime chart. The unrestricted 10–11 interval remains open.
