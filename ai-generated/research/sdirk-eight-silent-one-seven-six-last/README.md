# Closing the last independent detected six-clock orientation

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, assume the only nonzero quadratic defect is at the individually weight-zero stage one. Among seven active physical stages there are six distinct active clocks, and the active restrictions of \(\boldsymbol h=(A-\gamma I)\boldsymbol g\) and \(C\boldsymbol h\) are independent. In the [Gauss-double chart](../sdirk-eight-silent-one-seven-six-anchored/README.md) the double lies at a Gauss root \(r\), its two amplitudes differ, and the singleton profile is a nonzero scale of \(p_0=L_4/(X-r)\).

**Result.** The last chart has exactly one active literal front, at a singleton; the reverse quadratic factor \(k\ne0\); and the other silent physical zero occupies the separate reverse-root clock \(z\), not equal to the literal silent front. This packet excludes it. Together with the [first anchors](../sdirk-eight-silent-one-seven-six-anchored/README.md), [additional one-front anchors](../sdirk-eight-silent-one-seven-six-one-front/README.md), [reverse-factor cuts](../sdirk-eight-silent-one-seven-six-reverse/README.md), and [shared-root and Gauss-front cuts](../sdirk-eight-silent-one-seven-six-shared/README.md), the independent detected seven-active/six-clock chart is closed. The dependent active-\(h,Ch\) chart and seven or more distinct clocks are not part of this result. The unconditional **10–11** interval is unchanged.

## Exact early projections

Normalize clocks by \(\gamma\) and cubic defects by \(\gamma^3\). Let \(a\) be the normalized active literal front (either of the two), \(H_a\) its actual nonzero defect, and write
\[
 P(Y)=H_a p_0(\gamma Y)/D,\qquad D=p_0(\gamma a)\ne0.
\]
Both physical rows four and five are on the actual pure-four profile, even if one is the sole silent at \(z\). This is the weighted \(\boldsymbol w\)-transport at that root, not an assumption that the literal silent front shares the profile. Use \(s,y\) for the two normalized clocks and \(H_4(s)\) for the literal three-tap defect. Row four cannot repeat either literal front. It also cannot have \(H_4(s)=0\): its actual \(Ah\) read is coprime to that cubic, and on the active profile \(Ah\) would then vanish.

For either \(v=\tau_4,Ah\), write \(q=v_{\rm front}/H_a\) and \(v_4(s)\) for the literal read. The exact padded factor gives
\[
 X_v(s)=\frac{v_4(s)-qH_4(s)}{s-a}.
\]
On row five its literal pure-four value is \(v_5^0(s,y)+d_v(s)H\), affine in its actual \(H\), by the three fixed strict clock moments at the predecessors. Its necessary equation with the anchored actual profile is
\[
 H_4(s)v_5^0(s,y)+H\{H_4(s)(d_v(s)-q)-X_v(s)(y-a)\}=0. \tag{1}
\]
These polynomials are exact, including the \(2H\) strict stage-one feed. If \(s=y=r/\gamma\), retain the actual respective defects: an unequal one requires \(H_4(s)d_v(s)-v_4(s)=0\) for both reads, and the two slope polynomials have no common zero outside the forbidden literal front clocks. Equality of defects would force exact padded taps and a literal duplicate. Thus at most one of rows four and five is an active \(r\)-copy.

* **Row four at \(r\).** Set \(s=r/\gamma\), keep its actual \(H_4(s)\), and put \(H=P(y)\) in (1). After clearing denominators, both polynomials have the exact padded factor \(y-a\); remove it. Eliminate \(y\) from this cubic pair. The guarded diagonal projection has degree 24.
* **Row five at \(r\).** Keep its actual \(H\) unknown in (1) and eliminate it by the two-by-two affine determinant. Set \(y=r/\gamma\). Row four has \(H_4(s)=P(s)\); remove the exact padded \(s-a\) factor from its cleared equation, obtaining \(\Phi(\gamma,s)\) of degree two in \(s\). Eliminate \(s\) to get diagonal degree 20.
* **Neither at \(r\).** Use \(\Phi(\gamma,s)=0\) and \(H=P(y)\) in (1). As above remove \(y-a\), then divide by \(y-s\) as polynomials in \(y\). The omitted remainder is exactly \(\Phi(\gamma,s)v_5^0(s,s)\); the replay verifies this polynomial identity. The two resulting quadratics in \(y\) give a resultant, followed by its resultant with \(\Phi\) in \(s\). The guarded raw diagonal degree is 66. Both divisors remove only impossible literal active singleton collisions; a sole early silent at the separate root cannot share either active clock.

All three projections use the exact quadratic front field adjoined the monic Gauss quartic for \(r\). [Replay](nong_front.py).

### Padding, leading and zero-defect branches

The exact row-four-\(r\) degree-24 projection splits into degree 5 and 19: only in the first can both cubics vanish at the forbidden \(y=r/\gamma\), and only there divide their exact factor out. The row-five-\(r\) projection splits into degree 5 and 15 in the same manner, now for the forbidden extra \(s=r/\gamma\) factor of \(\Phi\).

When neither early row is \(r\), preserve the exact leading-\(\Phi\) degeneracy separately. This gives a degree-three diagonal piece where the true \(\Phi\) is linear, rather than blindly normalizing it as quadratic. There is also a degree-nine diagonal locus where \(H_4(s)=0\) and \(p_0(\gamma s)=0\), which the initial denominator-cleared pure reads would otherwise retain. On exactly that locus take the exact gcd of \(\Phi\) and \(H_4\) in the finite diagonal algebra and remove the common \(s\)-factor; the actual earlier \(Ah\) read already forbids it. The other retained diagonal polynomial has degree 30 after saturation of repeated roots of the forbidden factors. This is not a modular guard deletion. [Replay](nong_parts.py) and [exact quotient](remove_h4.py).

## Root-free tails and ordinary moments

The terminal is \(x=1-\gamma\). The projected diagonal bases first exclude \(x=r\) by checked units. Write \(c=x-\gamma u,\ d=x-\gamma(2-u)\) in star or \(x-2\gamma u\) in arithmetic, with \(k=1+2u-u^2\). When both nonterminal tails are physically active singletons, their actual affine-root equations can eliminate the unknown \(z\). For star let \(v=u-1,\ Y=x-\gamma\). The relation
\[
 (1-v)p_0(Y-\gamma v)-(1+v)p_0(Y+\gamma v)+2v(2-v^2)p_0(x)=0
\]
has exact factor \(-2v(v^2-1)\), whose roots are literal tail collisions. Its remaining diagonal cubic
\[
 [X^3]p_0\,\gamma^3+\gamma^2([X^2]p_0+3[X^3]p_0\,Y)+p_0(x)
\]
is a unit in the early projected bases. In arithmetic set \(H=-2+u+4u^2-u^3,\ T=4u^3-12u^2+3u+2\). The necessary equation \(H p_0(d)+2T p_0(c)-kT p_0(x)=0\) has the exact spurious factor \(u\) and a remaining quartic. In that gap quotient, the five active pegs given by the active front, \(x,c,d,r\) leave only one singleton, and the signed rank-one minor is a unit. No actual amplitude at \(r\) was used in either singleton tail test. [Replay](nong_tail.py).

If a nonterminal tail is \(r\) its fixed clock equation gives \(u\), and the other singleton comparison recovers the separate root \(z\) from its actual nonzero affine coefficient. A silent eighth is the sole separate silent, with \(z=x+\gamma k(u-2)/2\). If ninth is singleton as well, its comparison then gives the exact cubic gap projection after cancelling \(u\); if ninth is \(r\) its gap is fixed without assigning a singleton amplitude. No weight normalization at the silent eighth is used.

Separate the literal possibilities: the sole silent is row four, row five, or neither. At an early silent use its \(z\) clock and actual transported profile in (1), but never count it as an ordinary peg. Each **active** unpegged singleton early clock is a new peg. The active \(r\)-copy is not counted twice, and \(r\) is included even if its ordinary aggregate is zero. With six known pegs use the two nodal degree-six/seven moments; with five use signed rank one.

In the remaining four-peg cases \(r\) occurs once early and once in the tail. The scaled nodal quadratic reconstructs the two remaining singletons. The [signed double mass law](../sdirk-eight-silent-one-seven-six-shared/README.md) applies with the actual tail amplitude from the homogeneous reverse equation, and with the literal \(H_4\) or unknown actual \(H_5\) at the early \(r\). For unknown \(H_5\), cross its affine mass equation with each actual affine equation (1), without choosing a slope merely because it is nonzero in a generic case. The finite replay additionally allows the literal marked sixth-row residual, when its required pivots are units. For the five-peg silent-eighth chart it can keep the sixth clock as either the remaining singleton (homogenize its one-node moment recovery) or the actual second \(r\)-copy (cross the affine marked-tap residual with the mass equation). It never interprets a zero mask or a silent weight as an invertible physical tap. [Replay](nong_check.py) and [cleared optional gate](nong_sparse.py).

## Verification

Run `python3 check_last_singleton.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the sibling repository proof tree. The exact monic diagonal and Gauss equations give a finite algebra before checking the residuals. At the verified split Gauss primes \((1129,203),(1559,529),(1783,79)\) (the pair is \((p,t)\)), the replay retains every irreducible residue factor of every exact diagonal component. The last two prime choices are only for the arithmetic front with its first literal front active, to avoid accidental residue-field pivot zeros. The selected leading coefficients of the gap and early-clock relations are units in their corresponding entire reduced bases, so each such relation admits a monic lift in that local branch. The final finite residual unit checks lift through those bases. Equivalently, extend a prime above the specified reduction of the quadratic/Gauss base to the algebraic projected coordinates, and then use the checked monic normalizations to retain each subsequent parameter. This does not require reducing any unknown tableau or unknown weights. A factor is removed in characteristic zero only when its physical guard is proved, not because it appears degenerate in the residue field.

The [native Lean receipts](../../lean/RKCert/ReviewedNative/SDIRK8GaussDoubleLastSingleton.lean) check the root-free arithmetic and star tail eliminations and the affine unknown-defect cross. They compiled with standard axioms on Lean/Mathlib 4.36.0. The chart geometry and finite replay are source-level.
