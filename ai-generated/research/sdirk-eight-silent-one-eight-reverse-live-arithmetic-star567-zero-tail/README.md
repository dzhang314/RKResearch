# Arithmetic front, star rear, zero centered tail, interior silent placement

Consider the [constant nonzero nine-site reverse numerator](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) for strict ten-stage SDIRK8 over a characteristic-zero field. First is the sole nonzero quadratic-defect stage and ordinarily silent. There are eight distinct ordinarily active clocks and an actual ninth reverse clock at the extra ordinarily silent stage, here physical **5, 6, or 7**. The front literals are arithmetic and the ordinary rear is star; physical eighth is ordinary. The regular actual cubic profile \(H\) is a genuine mixed quintic, and the centered rear tail \(A+Bv^2=0\) is identically zero, \(A=B=0\). This packet excludes exactly these three placements. Literal silent 2/3/4, other rear phases, and the unrestricted **10–11** interval are not covered.

The [centered zero-tail identities](../sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail/README.md) use only the rear star read and a genuine quintic, not the front phase. They give \(H=\rho H_g\), where
\[
H_g=-8P L_3+(162\gamma-45)Q L_4+5Q L_5,
\quad Q=1-12\gamma+60\gamma^2-120\gamma^3,
\]
\(P\) is the same degree-five polynomial there, and \(Q(\gamma)\ne0\) by the exact gcd and genuine quintic. For this arithmetic front,
\[
 A_0=2+2t,\qquad B_0=3+4t,\qquad m_0=\tfrac12+3t,\qquad 2t^2=1.
\]
The true literal amplitudes are \(H_a=(A_0-1)/2,H_b=(B_0-1-m_0)/2\). The literal agreement
\[
 J(\gamma)=H_b H_g(\gamma A_0)-H_a H_g(\gamma B_0)=0
\]
now has full degree **eight** over \(\mathbb Q(t)\). The exact replay verifies its full coefficient shape, without dividing any nonconstant factor of \(J\). The normalization \(H=H_a H_g/H_g(\gamma A_0)\) is lawful because the actual literal amplitude is nonzero. It is also checked as a unit over the entire reduced diagonal. The actual fourth \(q=\gamma s\) must satisfy \(H(\gamma s)=H_4(s)\); the full degree-five left difference has the two exact padded roots \(s=A_0,B_0\), forbidden at this ordinary distinct fourth. The monic remaining cubic in \(s\) retains all roots.

The known ordinary pegs are \(\gamma A_0,\gamma B_0,\gamma s,x,c,d\), where \(x=1-\gamma\), \(m=1-2\gamma\) and \(c,d=m\pm\gamma v\). Write \(w=v^2\) and
\[
 E(X)=(X-\gamma A_0)(X-\gamma B_0)(X-\gamma s)(X-x)
             ((X-m)^2-\gamma^2w).
\]
The full monic ordinary nodal polynomial is \(E R\) for a monic missing quadratic \(R\). Only the paid ordinary scalar precision **seven** is needed: coefficients of \(X^1,\ldots,X^4\) in \(H W_{ER}-ER W_H\) must be zero. The resulting four-by-three coefficient matrix has its true monic kernel, hence all its \(3\times3\) minors vanish. Each minor has degree at most three in \(w\); no fifth gate, no ordinarily silent clock counted as a peg, and no ordinary precision above seven is used.

At \(p=1129,t=203\), the degree-eight diagonal retains both complete components of degrees 1 and 7. In each field the literal normalization and leading coefficient of the actual fourth cubic are units. On each **full** fourth cubic algebra, the first minor has cubic leading unit, and the second minor is a unit modulo that first monicized cubic. The products of unit multiplication determinants thus certify all roots in the finite free local model, not just sampled points. A characteristic-zero candidate would have a place at this chosen reduction of its embedded \(\mathbb Q(t)\) and one of these complete monic fibers. No claim about its weights or field ordering is needed.

Install `sympy==1.14.0` and `python-flint==0.9.0`, then run `python3 check_arithmetic_star567_zero_tail.py` from this directory with the declared siblings. The [zero-tail coefficient identities](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStar4ZeroTail.lean) and [generic missing-quadratic minor and unordered-pair statements](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStarInteriorZeroTail.lean) are the reusable native gates, previously checked on Lean/Mathlib 4.36.0; the new arithmetic exclusion is exact source-level.
