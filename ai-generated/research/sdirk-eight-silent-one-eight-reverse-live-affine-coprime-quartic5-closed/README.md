# Six true ordinary pegs, affine-coprime quartic with silent fifth

This excludes all four front/rear orientations with **actual ordinarily silent physical fifth** in the [strict ten-stage SDIRK8 affine-coprime quartic chart](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed/README.md). The field has characteristic zero. Physical one is the sole nonzero quadratic-defect row and has no ordinary or reverse contribution. Eight ordinary physical rows have distinct clocks. Actual fifth has no ordinary weight but has a genuine nonzero reverse read at the distinct ninth clock \(z\). The reverse numerator \(T\) is nonconstant affine, the mixed numerator \(S\) has degree at most four, and \(S,T\) are coprime. Both literal front types and both ordinarily weighted eighth rear types are tested, independently. No ordering is used. Actual silent 6, 7, and 8, different profile degrees, and other support charts are separate. The unrestricted strict SDIRK8 interval remains **10–11**.

## A small homogeneous ordinary determinant

The [companion chronology and ordinary deflation](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed/README.md) give the true profile \(H(X)=\gamma\Delta L_4(X)/Q(X)\) and
\[
 \mathcal B(D_8)=L_4 W_{D_8}-D_8 W_{L_4}=\lambda Q^2,\quad
 W_D(X)=I_Y\!\left(\frac{D(X)-D(Y)}{X-Y}\right).
\]
Only scalar precision through degree seven is used. For any \(D\) of degree at most eight, \(\deg\mathcal B(D)\le3\): in its joined divided difference, the term with \(L_4(Y)\) is killed for \(Y\)-exponents 0–3 by the four true quartic moments, and the remaining exponents have total degree at most seven before multiplication by \(L_4(Y)\). The term with the difference of \(L_4\) already has \(X\)-degree at most three.

Here \(a,b,q=\gamma s,x,c,d\) are six **ordinary** clocks, with \(s\) the true ordinary physical fourth, and \(d=c_8\). Let \(E\) be their monic nodal polynomial. Then \(D_8=E(X^2+r_1 X+r_0)\). The matrix of coefficients \([X^0],\ldots,[X^3]\) in the four columns
\[
 \mathcal B(E),\quad \mathcal B(XE),\quad \mathcal B(X^2E),\quad Q^2
\]
annihilates \((r_0,r_1,1,-\lambda)^{\mathsf T}\). Its determinant is zero with no inverse of any cofactor, leading amplitude, or guessed Padé rank. The source computes its transpose, with the same determinant, and verifies the discarded high coefficients are identically zero. The raw determinant has degrees \((\deg_u,\deg_s,\deg_\gamma)=(6,3,28)\). Divide only the true nonzero early profile values \(L_4(a)L_4(b)\) to obtain \(P\) of degrees \((6,3,20)\). This necessary projection by itself also applies when physical silent is 6 or 7, but the present final test does not.

## Exact projections, with all leading cases retained

Let \(J(\gamma,s)\) be the true fourth quadratic quotient, after its two forbidden literal pads, and \(F(\gamma,u)\) the ordinary eighth rear shape, after the allowed collision pads. These are the true \(J,F\) from the [silent-fourth companion](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic4-closed/README.md), **not** that companion's equation substituting \(z/\gamma\) for \(s\). The exact \(\operatorname{Res}_s(J,P)\) has bidegree \((12,52)\) in \((u,\gamma)\). Divide its exact factor \(R_{12}\), the coprime \(Q,L_4\) guard from the literal 2/3 companion, giving \(N(\gamma,u)\) of bidegree \((12,40)\). The exact \(\operatorname{Res}_u(F,N)\) then has diagonal degree 248 or 368 for the star or arithmetic rear. The only removed factors are
\[
 \gamma^{24}L_4(a)^4 L_4(b)^4 R_{12}^{\,4}.
\]
Those are nonzero over the original coefficient field, not inferred from the residue test. The monic retained diagonal \(M\) has full degree **144** or **264**. Both resultants are exact bounded-CRT computations with their full Sylvester degrees, so specialize to zero at every actual common root, including simultaneous leading drops.

## Actual ordinarily silent fifth, not a missing ordinary root

Use \(x=1-\gamma,\ c=x-\gamma u,\ k=1+2u-u^2\) and the actual physical silent-clock comparison at the penultimate row, with \(z\) the actual **fifth** clock. For \(R=(L_4(c)Q(x)-k L_4(x)Q(c))/u\), that comparison forces
\[
 Y=\frac z\gamma=\frac{xR+\gamma k L_4(x)Q(c)}{\gamma R}.
\]
The denominator is genuinely nonzero because \(u,\gamma,k,L_4(x),Q(c)\) are nonzero. No claim \(Y=s\) is used. The normalized amplitude at \(Y\) can vanish, for example if the ordinarily silent clock is a Gauss root; we never divide by \(L_4(z)\). The actual fourth retains its own clock \(s\) and its actual \(H_4(s)\).

In the [literal rows 2–5 determinant](../sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed/README.md#full-finite-fibers-and-actual-fifth), insert this actual silent fifth clock and actual rational amplitude. Clear by \(Q(\gamma Y)\) and divide only the exact pads \(Y-A,Y-B,Y-s\), nonzero by distinctness. This yields the actual fifth gate \(J_5(Y)=0\), independent of the ordinary determinant \(P=0\). We do not assign an ordinary mass or a missing ordinary root to fifth.

## Complete good reduction and replay

At \((1129,t=203)\), every reduced factor of the full monic \(M\), with its full multiplicity, is retained. The ordinary rear shape \(F\) and ordinary fourth \(J\) have their full leading units on every relevant component; use the whole reduced gcd of \(F,N\) and both ordinary fourth roots algebraically, even when repeated. In these finite algebras the actual silent-fifth denominator and literal predecessor denominators are checked as units wherever needed. The pair \(P,J_5(Y)\) has a unit combination. The four component counts are **4, 19, 4, 10**; the corresponding weighted gap/fourth dimensions are **576, 528, 576, 528**. Each of the 37 components is excluded by the joint test. Finiteness over the localized integral base lifts the units before characteristic zero, as in the literal 2/3 companion. No assertion that an actual unknown tableau reduces at this prime is needed.

Run `python3 check_eight_reverse_live_affine_coprime_quartic5.py` next to the earlier literal companions, with `sympy==1.14.0` and `python-flint==0.9.0`. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineQuarticSixPegs.lean) checks the linear truncated moment read and Bézout map and proves the monic-quadratic coefficient-matrix implication over **arbitrary commutative rings**, without needing a pivot. It verifies on Lean/Mathlib 4.36.0. The actual chronology, quartic degree restriction, and exact CRT/fibers are source-level; the complete tableau exclusion is characteristic zero, not a native arbitrary-ring claim.
