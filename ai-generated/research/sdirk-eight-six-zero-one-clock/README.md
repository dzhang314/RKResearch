# Six zero rows cannot leave only one physical off-zero clock in characteristic zero

Consider a strict ten-stage SDIRK tableau with common nonzero diagonal \(\gamma\), of ordinary order at least eight over a characteristic-zero field. Write \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), and \(G=\operatorname{diag}\mathbf g\). Assume exactly six physical entries of \(\mathbf g\) vanish, and all four other rows have a common clock.

**Result.** This entire one-off-clock stratum is impossible in characteristic zero, both with canceled and nonzero net ordinary mass at the off clock. This is not an exclusion of all six-zero cases or a new overall stage bound.

## 1. Rank and actual phase anchors

Use the [two-sided saturated flags and support formula](../sdirk-eight-two-zero-line/README.md), with \(U=\ker G\) and \(d_j=\dim(E_j\cap U)\). The \(W_j\) off restriction rank is \(\dim W_j-6+d_{5-j}\). If the four nonzero residuals were all equal, the off restriction of \(E_2,E_3\) would have rank one, so the \(W_2\) off restriction would have rank three. With no active off weight it has rank at most one, the dimension of \(Z_2\); with an active off weight it also has rank at most one, since weighting maps \(E_2\) isomorphically to \(W_2\) and every off-clock read is constant. This is impossible. With nonconstant residuals the \(E_2,E_3\) off ranks are both two, hence \(d_2=2,d_3=4\). In particular \(W_2\) off rank is two; active off weights with different nonzero residuals are necessary.

Let \(B=\sum_{\mathrm{off}} b_i\) be the ordinary aggregate at that one clock. The pure residual moments \(\sum_{\mathrm{off}}b_i g_i^j=0\) for \(j=1,2,3\) force **all four off rows to carry nonzero weights**. For \(B=0\) apply the residual Vandermonde through degree three: each of at least two live residual classes has zero aggregate and at least two live rows. For \(B\ne0\), fewer than four distinct nonzero live residuals would force all class aggregates zero (use powers \(1,\ldots,r\) for \(r\le3\)). Thus the two cases are two canceled residual pairs, or four distinct nonzero live residuals.

The first physical row is off-zero, at clock \(\gamma\). The terminal pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\) is proportional to the nonzero \(\mathbf b^\mathsf T G\); its last coordinate is nonzero. Thus physical row 10 is off-zero too, at clock \(1-\gamma\), by the [literal reverse suffix](../sdirk-eight-four-zero-gaussian-rear/README.md). Hence \(\gamma=1/2\). The first and last three literal clocks are distinct at their respective ends. Row 8 cannot be silent (the reverse ghost would require \(z_8\ne0\)). Consequently rows 2,3,8,9 are four fixed literal zero anchors, and rows 8,9 are live.

Write \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(N'=A'-I\), and let \(d=1\) be the normalized off clock, with normalized endpoint \(D=2\). Both second quadratic ratios are zero. Let the signed forward and reverse gaps be \(u,v\), both roots of \(T^2-2T-1\). The actual four anchor clocks in physical order \(2,3,8,9\) are
\[
 a=1+u,\quad b=1+w_F,\quad s=1-w_R,\quad t=1-v,
\]
where \(w_F=2u\) or \(2-u\), and \(w_R=2v\) or \(2-v\). The five values \(a,b,s,t,d\) are pairwise distinct in every exact frame. If the third literal phase has gap \(w\) and second gap \(\xi\), its first strict tap \(p\) satisfies
\[
 2p\xi=2w\xi+1+2w-w^2.
\]
Indeed the second strict tap is \(w-p\), and the actual normalized third quadratic residual is zero. This first tap is nonzero: the right side is \(1+4\xi\) in arithmetic and \(-2\) in the star. Write \(p_F,p_R\) for the two taps. All eight choices (same or opposite roots \(v\) of the quadratic, and each ordered pair of literal phases) are retained.

## 2. Canceled aggregate: a six-site barycentric contradiction

Let \(\boldsymbol\eta^{\mathsf T}=\mathbf z^\mathsf T N'\in Z_3=\operatorname{Ann}(E_4)\). The \(W_3\) off restriction rank is \(d_2=2\), spanned by the independent restrictions of \(\mathbf b^\mathsf T\) and \(\mathbf b^\mathsf T G\). Since \(\eta_{10}=0\), on the off rows \(\eta_i=\beta b_i(g_i-g_{10})\) for one scalar \(\beta\). Thus the **off aggregate of \(\boldsymbol\eta\)** is zero when \(B=0\); no claim of coordinatewise off vanishing is needed. All scalar moments of \(\boldsymbol\eta|_U\) through degree four vanish.

The two rear pure values are nonzero, and have
\[
 \frac{\eta_8}{\eta_9}=\frac{b_8p_R}{b_9v}.
\]
This follows from the literal weighted reflected taps from physical row 10, with \(z_8=z_9=0\). If there were at most five distinct literal zero clocks, the vanishing moments would force the \(\eta\) aggregate at each to vanish. Since \(s,t\) are distinct, their two nonzero pure values would require a duplicate of each among the two other physical zero rows; thus all six zero rows use only \(a,b,s,t\). The ordinary rank would force four live Gaussian sites, but \(L_4(a)\ne0\) in the quadratic gap field. Therefore all six literal zero clocks are distinct.

The two unknown clocks are the roots of the monic quadratic from the masked ordinary \(2\)-by-\(2\) Hankel recurrence, using \((T-a)(T-b)(T-s)(T-t)\). Its pivot is checked nonzero in all eight fields; all moments used have degree at most seven. Write \(P_6(T)\) for the resulting polynomial on all six literal zero nodes. The vanishing of the first five moments of \(\boldsymbol\eta|_U\) means
\(\eta_i=\alpha/P_6'(x_i)\) for a single nonzero \(\alpha\), by the six-node Vandermonde nullspace. Ordinary weights, including possibly silent ones, are
\[
 b_i=\frac{I(P_6(T)/(T-x_i))}{P_6'(x_i)},\qquad
 I(T^j)=\frac{2^j}{j+1}.
\]
Substituting the literal ratio above gives
\[
 p_R I(P_6/(T-s))=v I(P_6/(T-t)).
\]
The exact polynomial calculation makes this false in all eight frames.

## 3. Nonzero aggregate: the virtual pure mode on seven ordinary labels

Assume \(B\ne0\). Mask \(d\) and the four fixed zero anchors to remove their ordinary masses even if any front anchor is silent. In every frame the exact ordinary \(2\)-by-\(2\) pivot of this degree-five mask, using degrees at most seven, is nonzero. The only remaining physical clock values are the other two zero rows; the pivot forces both to be live, distinct, and outside the five anchors. Thus there are seven pairwise distinct **literal** scalar labels, with aggregate \(B\) at \(d\), though the first two zero weights could initially be zero.

Take \(\mathbf f=N'\mathbf g/g_1\in F_3\). Its normalized physical values at rows 2 and 3 are \(u,p_F\). The pure row with entries \(b_i f_i\) belongs to \(Z_3\). If it were proportional to \(\mathbf z^\mathsf T\), its first coordinate would force it to be identically zero, since \(f_1=0\) and \(b_1g_1\ne0\). Then both first two zero rows would be silent by their nonzero taps. The ordinary measure would be supported on \(d,s,t\) plus the two free zero clocks; its masked \(3\)-by-\(3\) Hankel determinant using mask \((T-d)(T-s)(T-t)\) would be zero. The exact determinant is nonzero in all eight frames, so the pure rows are independent.

It follows that \(\boldsymbol\eta\) is a linear combination of \(\mathbf z\) and the row \(b_i f_i\), with nonzero coefficient of the latter. On \(U\), where \(z_i=0\), this enforces
\[
 v f_8=p_R f_9
\]
with both entries nonzero. On the four off rows, \(f_i\) is affine in \(g_i\) because \(E_3\) off rank is two, with bases \(1,\mathbf g\). Replace those rows by the single virtual ordinary node \(d\) with weight \(B\) and virtual value \(f(d)\) given by the constant term at \(g=0\). The residual moments of degrees one and two show this replacement preserves both the weighted first and second powers of \(\mathbf f\). Consequently the virtual weighted pure mode annihilates scalar powers through degree four, and also satisfies the genuine pure-square equations
\[
 \sum_i b_i f_i^2=0,\qquad \sum_i b_i x_i f_i^2=0
\]
on the seven literal scalar labels. Neither equation uses a reverse squared pairing or a sign assumption.

## 4. Exact projection with the ordinary cardinal numerators

Let \(P_7(T)=P_5(T)(T^2+kT+q)\) be the monic polynomial of the seven labels, where \(P_5\) is the five-anchor mask. The moment \(I(P_7)=0\) gives one affine relation in \(k,q\), leaving one scalar parameter. For each label define its cardinal numerator
\[
 B_i=I(P_7(T)/(T-x_i)),\qquad b_i=B_i/P_7'(x_i).
\]
The rows annihilating clock powers through degree four have dimension two; they are exactly \((A_0+A_1x_i)/P_7'(x_i)\), by polynomial interpolation. Thus the virtual pure mode has \(f_i B_i=A_0+A_1x_i\), including at a possibly silent label. The values \(u,p_F\) at \(a,b\) determine \(A_0,A_1\) as linear functions of \(k,q\). The rear ratio gives the quadratic scalar gate
\[
 v(A_0+A_1s) B_t-p_R(A_0+A_1t)B_s=0.
\]
It is nonzero of degree exactly two in all eight frames. Its complete factorization over the quadratic gap field gives eleven factors in total, of degrees one or two. At each exact factor the five known weights are nonzero, the two free clocks are distinct and avoid the anchors, and all ordinary numerator inverses are checked in the seven-node algebra. This treats algebraic roots and possible silent anchors explicitly.

Finally define \(B(X)=I_T((P_7(T)-P_7(X))/(T-X))\). At a root \(x_i\) of \(P_7\), this is \(B_i\), so the pure-square moment of index \(j\) equals the degree-six coefficient of
\[
 (A_0+A_1X)^2 X^j B(X)^{-1}\pmod{P_7(X)}.
\]
This is the ordinary interpolation leading-coefficient identity, checked after an exact inverse of \(B\). For \(j=0,1\) both coefficients are nonzero in each of the eleven residue fields. Thus no actual candidate can satisfy the pure-square gates.

Run `python check_canceled.py` and `python check_noncanceled.py` with SymPy 1.14. The source includes both real and nonreal algebraic possibilities, without numerical real-root tests. The literal saturated and weighted-primitive ingresses are the mathematical proofs cited above; the exact polynomial replays are not an end-to-end native `HasOrder` theorem.
