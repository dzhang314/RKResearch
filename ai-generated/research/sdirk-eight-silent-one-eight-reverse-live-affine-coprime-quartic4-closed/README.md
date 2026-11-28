# Affine coprime quartic, actual reverse-live silent fourth

This excludes the four literal front/rear orientations with silent \(\zeta=4\) in the [strict ten-stage SDIRK8 affine-coprime quartic chart](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed/README.md). The field has characteristic zero. Physical one is the sole nonzero quadratic-defect row and is ordinarily and reversely silent. Eight ordinary physical rows have pairwise distinct clocks. Actual physical fourth is ordinarily silent but reverse-live, at a ninth distinct clock. The nine-site numerator \(T\) is nonconstant affine; \(\deg S\le4\) and \(S,T\) are coprime. Both literal front phases and both ordinarily weighted eighth rear phases are covered. Physical silent 5–8, all other numerator profiles and other support charts remain separate. No ordering is used, and the unrestricted **10–11** interval is unchanged.

## Recover the actual silent fourth from the penultimate row

Write \(a=\gamma A,b=\gamma B,x=1-\gamma,c=x-\gamma u\), \(k=1+2u-u^2\), and \(z=\gamma s\), with \(\gamma,u,k\ne0\). The two literal early reads give the companion's true profile \(H(X)=\gamma\Delta L_4(X)/Q(X)\). Use \(P_i=L_4(i)\) and \(Q_i=Q(i)\). The actual penultimate comparison is
\[
 (x-\gamma s)P_cQ_x=k(c-\gamma s)P_xQ_c.
\]
It forces
\[
 uR=P_cQ_x-kP_xQ_c,\qquad
 (\gamma R)s=xR+\gamma kP_xQ_c.
\]
The first is an exact polynomial definition of \(R\): the right-hand polynomial vanishes at \(u=0\). The second is an actual scalar identity by the comparison and \(u\ne0\). It also proves \(\gamma R\ne0\), since \(k,P_x,Q_c,\gamma\) are nonzero by the actual chronology and coprime profile. No formal or numerical generic-leading hypothesis replaces this proof.

The actual normalized fourth has its two-padded degree-at-most-two equation \(J(\gamma,s)=0\) from the two literal fronts and \(H_4(s)\). The removed factors \(s-A,s-B\) are nonzero because fourth has its own distinct reverse-live clock. Set \(n=xR+\gamma kP_xQ_c,\ d_0=\gamma R\). The homogeneous polynomial
\[
 G(\gamma,u)=J_0d_0^2+J_1nd_0+J_2n^2
\]
is necessary including when \(J_2\) vanishes. It has exact bidegree \((\deg_u,\deg_\gamma)=(6,24)\). Independently use the companion's ordinary eighth shape \(F\), with \((2,14)\) in the star rear, \((5,14)\) in the arithmetic rear. This divides only \(u(u-1)(u-2)\) for the star and \(u^2\) for the arithmetic rear, all true nonzero factors in their indicated phases. The exact diagonal projection \(\operatorname{Res}_u(F,G)\) has degree 132 or 204 using the bounded split CRT. This is the padded exact resultant, so a characteristic-zero pair of roots cannot escape at a degenerate tail leading value.

From that projection the replay divides only the exact factors
\[
 \gamma^{12}\ \text{or}\ \gamma^{14},\qquad L_4(a)^2 L_4(b)^2,\qquad Q(x)^4,\qquad R_{12}^{\,2}.
\]
Here \(R_{12}\) is the degree-twelve common-root guard from the literal 2/3 companion: it divides the degree-20 polynomial \(q_1^4 L_4(-\gamma q_0/q_1)\), not a condition inferred from a residue test. The other factors are genuinely nonzero by actual chronology, early profile values, and absence of a terminal pole. The full retained monic diagonal has degree **60** or **130**.

## Five true ordinary pegs and the literal next row

The five known ordinary pegs are \(a,b,x,c,d\), where \(d=c_8\) is the actual third rear ordinary clock. **Do not include \(z\)** in the ordinary nodal factor. The same deflated identity \(L_4 W_{D_8}-D_8W_{L_4}=\lambda Q^2\) uses only ordinary scalar precision seven. The companion's five-by-five Padé-style Cramer matrix recovers the ordinary nodal polynomial; division by the five actual pegs leaves the normalized missing monic cubic. Actual physical five is ordinary. Its root must satisfy the literal 2–5 determinant, where its predecessor physical fourth is exactly \(s=n/d_0\) and has its **actual** amplitude \(H_4(s)\). This step does include that silent fourth row's true amplitude and row transports. The prospective fifth determinant is cleared by \(Q(\gamma Y)\) and then divided only by its exact literal pads \(Y-A,Y-B,Y-s\). No ordinary weight at physical fourth or equality of virtual and actual amplitudes is used.

The single good reduction \((1129,t=203)\) preserves the monic retained diagonal and the complete degree-two or degree-five leading shape on every component. The replay imposes the full reduced gcd of \(F,G\), not a selected gap. Over that complete algebra \(\gamma R\) is a unit; the reconstructed \(s\) satisfies the exact quotient \(J\), and the Cramer determinant and literal predecessor denominators are units. The final multiplication determinant on the missing cubic is a unit. The four component counts are **4, 4, 4, 6**, with full diagonal multiplicities retained. These checked units lift by finiteness over the localized coefficient ring as in the companion. We do not assume any a priori good reduction of a tableau or drop accidental collision or leading-zero fibers.

## Replay and Lean

Install `sympy==1.14.0` and `python-flint==0.9.0`. Run `python3 check_eight_reverse_live_affine_coprime_quartic4.py` in this directory, next to the literal 2/3 companion and its declared dependencies. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineQuarticSilentFourth.lean) verifies the guarded reconstruction, including actual denominator nonvanishing, and the homogeneous degree-two projection on Lean/Mathlib 4.36.0. The saturation bridge and exact CRT/fiber computation remain source-level.
