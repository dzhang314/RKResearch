# Sole genuinely nonliteral fourth transport: exact finite profiles

This is a **finite-profile reduction, not an exclusion**. Use the detected seven-distinct active strict SDIRK8 chart at ten stages over a characteristic-zero field, only first physical quadratic defect nonzero and weight zero, \(k\ne0\), and a nonconstant coprime affine profile. Exactly one literal front \(a\) is ordinarily active. The other \(b\) is physically silent with zero reverse weight. The sole nonliteral separate reverse contributor is physical fourth, at \(z=\gamma s\). The actual fifth and eighth are ordinary active, with either star or arithmetic rear. There is no statement about the other nonliteral silent positions or the global **10–11** interval.

## Two honest front anchors

Use normalized clocks and cubic defects. The actual fourth \(s\) has its own literal polynomial value \(H_4(s)\), and by sole reverse transport that stage's actual defect and its pure-four reads agree with the transported rational/affine profiles. Here \(H_4(s)\ne0\): otherwise its proportional actual \(Ah\) would also vanish, contrary to the exact gcd of the two literal fourth polynomials. This gcd is replayed here and is the same [pure-read guard as in the constant chart](../sdirk-eight-silent-one-seven-distinct-constant-nonliteral/README.md). The ordinary active literal \(a\) has known \(h_a\ne0\). Their two distinct actual clocks directly determine the affine denominator up to scale:
\[
 Q(Y)=H_4(s)L_4(\gamma a)(s-Y)
       +h_a L_4(\gamma s)(Y-a),\qquad
 P(Y)=h_aH_4(s)(s-a)L_4(\gamma Y).
\]
Then \(Q(Y)h(Y)=P(Y)\) at the ordinary active sites and at the sole transported actual fourth. The physically silent literal \(b\) is not assigned this profile.

Use \(a,s\) as the two anchors for both actual pure-four slopes. As in the [finite arithmetic front elimination](../sdirk-eight-silent-one-seven-distinct-coprime-no-front-arithmetic/README.md), cross elimination of the actual fifth defect gives a primitive exact \(D(s,y)\) of bidegree \((3,3)\) independent of \(\gamma,u\). Substitute \(Qh=P\) into the first pure-four equation and remove only exact padded factors \(y-a,y-s\) and true nonzero \(s\)-factors. The genuine fifth \(y\) is a common root, so the padded \(y\)-resultant \(J(\gamma,s)\) vanishes. Its \(s\)-degree is 16 for star literal front or 26 for arithmetic literal front; its \(\gamma\)-degree is 12. In both cases its \(s\)-coefficient gcd is one over \(\mathbb Q(t)[\gamma]\), \(t^2=1/2\).

## Independent rear eliminant

Write \(q(X)=\gamma Q(X/\gamma)\), \(x=1-\gamma,\ c=x-\gamma u\), and \(k=1+2u-u^2\). The ordinary reverse ratio fixes the actual ninth cross
\[
R_9=q(x)(x-z)L_4(c)-k\,q(c)(c-z)L_4(x)=0.
\]
After only exact guarding factors including the forbidden \(u=0\), its \(u\)-degree is three. For actual \((\gamma,s)\) the raw cross cannot vanish identically in \(u\): substitute the gap giving \(c=z\) to leave the nonzero \(q(x)(x-z)L_4(z)\). A factor divided from it is nonzero at a genuine gap, so the remaining gap equation passes the same finiteness test.

For a star rear, \(d=x-\gamma(2-u)\), and the actual eighth requires the same ninth cross with \(u\mapsto2-u\). Write \(v=u-1\); the cubic separates as \(A_0+A_1v^2+v(B_0+B_1v^2)\). Since \(v\ne0\), both affine expressions at \(v^2\) must vanish. The necessary cross \(K=A_0B_1-A_1B_0\) has \((s,\gamma)\)-degrees \((8,19)\), even if both affine slopes vanish. No assumption of a slope unit enters this finite deduction.

For an arithmetic rear, \(d=x-2\gamma u\). With \(H=-2+u+4u^2-u^3\) and \(T=4u^3-12u^2+3u+2\), the other actual reflected ratio requires
\[
 H q(x)(x-z)L_4(d)+kTq(d)(d-z)L_4(x)=0.
\]
Here \(2(c-z)-(x-z)=d-z\). After exact forbidden factors, eliminate \(u\) by the padded resultant with the ninth cross. That \(K\) has \((s,\gamma)\)-degrees \((36,85)\), without assuming the actual leading coefficient survives specialization.

## Finiteness and verification

The exact specialization \(\gamma=1\) preserves nominal \(s\)-degrees of \(J,K\) and gives \(\gcd(J,K)=1\) in every one of the eight literal/rear orientations. Thus their padded diagonal resultant is nonzero as an exact polynomial. This test value is not assumed to be a possible RK diagonal. There are finitely many \(\gamma\), then finitely many actual \(s\) by the primitive content of \(J\), finitely many \(u\) by the nonzero ninth cross at each actual specialization, finitely many \(y\) by the primitive \(y\)-content of \(D\). The five ordinary active pegs are \(\gamma a,x,c,d,\gamma y\), **not** the transported fourth. The signed two-node moment mask of the [seven-distinct anchors](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) then gives finitely many assignments of the two remaining ordinarily active clocks, and the first seven moments determine their weights along with the five known-site weights. This is no claim of finite tableau entries or of any realized profile.

Run `python3 check_nonliteral_fourth_finite.py` in the sibling research proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. The replay checks all exact polynomial contents and eight exact specializations. The [Lean supporting lemmas](../../lean/RKCert/ReviewedNative/SDIRK8NonliteralFourth.lean) check the even/odd star implication and the nonzero raw ninth cross at the transported clock on Lean/Mathlib 4.36.0. To close this chart, explicitly reconstruct the two-rear diagonal carriers and retain other admissible fourths at any true terminal/pole contact, rather than removing their entire diagonals based on finite-reduction artifacts.
