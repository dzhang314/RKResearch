# A single-valued cubic defect forces eight distinct physical zero clocks

Use the [all-active half-diagonal endpoint pair](../sdirk-eight-half-equal/README.md) of a proposed ten-stage strict SDIRK8 tableau over a characteristic-zero field. Let \(\boldsymbol h=(A-\gamma I)\boldsymbol g\), with only the two endpoints off the quadratic-zero set \(U\). Suppose \(h_i\) is single-valued at every zero clock, meaning \(h_i=h_j\) whenever \(c_i=c_j\) for \(i,j\in U\). This covers coprime rational profiles with no physical poles but is not limited to them.

**Result.** The eight physical zero clocks are distinct. In the coprime monic quadratic chart they also satisfy a simple polynomial Bézout moment identity, with none of their cubic defects zero. This restricts the surviving chart, not the unrestricted **10–11** stage interval.

## 1. Clock twins and the two-receiver obstruction

By the [single-valued support census](../sdirk-eight-half-rational/README.md), there are seven or eight ordinary distinct zero sites without canceled groups. If there are seven, exactly one physical pair has a repeated clock, with the same \(h\) by hypothesis. The four pegged front/rear zero clocks in physical positions \(2,3,8,9\) are distinct. Orient the tableau so the later member of the pair is at physical position at most seven: in the forward direction its index is \(j\), and in the reversed direction it is \(11-i\) for \(i<j\). If both indices exceeded seven, the two rows would be among the four distinct pegged rows. The weighted reflection preserves \(g=0\) on \(U\), all activity and equality of \(h\) within a zero-clock group, because the reverse cubic-defect normalization is a nonzero multiple of \(\boldsymbol h\).

In this orientation compare the later row to the earlier row with zeros inserted for the unused predecessor taps and with its diagonal put at the later index. Since both clocks and both \(h\)'s agree, the padded earlier row has the same donor tap \(h_i/g_1\) (stage one). The other strict taps have equal moment reads on \(1,X,X^2,X^3\):
* The first three are the row sum, clean quadratic read, and the pure cubic relation \(A\boldsymbol c^{\odot2}-\boldsymbol c^{\odot3}/3=(2/3)(\boldsymbol g+\boldsymbol h)\), with the common diagonal and donor subtracted.
* The fourth follows because \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) belongs on \(U\) to the pure span \(\langle\boldsymbol h,C\boldsymbol h,L_4(\boldsymbol c)\rangle\). Its value depends only on the pair \((c_i,h_i)\).

When the later row is at position at most six, the at-most-four earlier zero clocks are distinct, so ordinary Vandermonde separates their taps. This is a literal twin, which can be merged and contradicts the ten-stage floor. At position seven, there are five distinct predecessor zero clocks. The two rows have the same additional strict-tap observation on \(\boldsymbol h\), because \(A\boldsymbol h\) lies in the same pure span. Unless the five predecessor \(h\) values agree with a scalar cubic \(P\), the five probes \((1,X,X^2,X^3,h)\) distinguish the five taps, again giving a literal twin.

It remains to handle the rank deficiency. The cubic \(P\) agrees with \(h\) on the five predecessor zero rows and the new repeated zero row, leaving only the two distinct rear pegged clocks \(c,d\), with nonzero \(h\)-values and weights. The paid defect moments give
\[
                         \ell\bigl(h(h-P)X^j\bigr)=0,\qquad j=0,1 .
\]
Indeed the \(h^2\) moments are paid through degree one, and \(P X^j\) has degree at most four for the linear \(h\)-moment. These two equations are supported on the two distinct rear sites. Vandermonde and their nonzero weights and defects force \(h=P\) there too. The ordinary and paid \(h\) moments now give \(I(P X^j)=0\) for \(0\le j\le3\), where \(I(X^j)=1/(j+1)\). The four-by-four Hilbert matrix is invertible in characteristic zero, giving \(P=0\) and contradicting the nonzero rear defects. This argument never needs real root positions or signs of weights.

## 2. Bézout moment reduction for a coprime quadratic

Now assume \(q(c_i)h_i=p(c_i)\), with \(\gcd(p,q)=1\), \(q\) monic quadratic, \(p\in\langle L_3,L_4,L_5\rangle\). Put \(D=\prod_{i\in U}(X-c_i)\), a squarefree monic degree-eight polynomial. Weighted Lagrange interpolation gives polynomials \(R,S\) with
\[
 R(c_i)=b_i h_i D'(c_i),\qquad S(c_i)=b_i h_i^2 D'(c_i),\qquad \deg R\le2,\quad\deg S\le5 .
\]
For any polynomial \(v\), the sum \(\sum v(c_i)/D'(c_i)\) is the coefficient of \(X^7\) in its remainder modulo \(D\); this is the ordinary Lagrange formula using the leading coefficients of the cardinal polynomials. Thus one successively removes the highest coefficients of \(R\) via \(v=X^j R\), \(0\le j\le4\), and of \(S\) using \(0\le j\le1\), by the paid moments.

The relation \(qS-Rp=0\) follows from eight distinct roots and degree at most seven. Therefore \(R=\lambda q\), \(S=\lambda p\), with \(\lambda\ne0\) because there are nonzero corner defects and weights. In particular \(h_i\ne0\) and \(p(c_i)\ne0\) for *every* zero physical row. For a polynomial \(f\) define
\[
                          W_f(X)=I_Z\!\left(\frac{f(X)-f(Z)}{X-Z}\right).
\]
By precision seven, ordinary Lagrange interpolation gives \(W_D(c_i)=b_i D'(c_i)\). At the eight clocks we now have \(pW_D=\lambda q^2\). The polynomial
\[
          \mathcal B_p(D)=pW_D-DW_p=I_Z\!\left(\frac{D(X)p(Z)-p(X)D(Z)}{X-Z}\right)
\]
has degree at most four. To see the degree bound formally, write \(E_f(X)=\sum_{j\ge0}I(X^j f)X^{-j-1}\); then \(\mathcal B_p(D)=D E_p-p E_D\). The first three coefficients of \(E_p\) vanish by Legendre orthogonality, so \(DE_p\) starts in degree four, and \(pE_D\) also starts in degree at most four. Hence the eight evaluations give the identity \(\mathcal B_p(D)=\lambda q^2\).

If \(P_6\) is the product of the six known literal factors \(a,b,s,y,c,d\), then \(D=P_6(X^2+uX+v)\). Linearity in \(D\) gives five scalar equations linear in \(u,v,\lambda\):
\[
          \mathcal B_p(X^2P_6)+u\mathcal B_p(XP_6)+v\mathcal B_p(P_6)-\lambda q^2=0 .
\]
In particular the three \(\mathcal B_p\) coefficient columns and \(q^2\) have rank at most three. This produces small polynomial elimination gates without a squared-denominator inverse or assumptions on the degree-five coefficient of \(p\). The moment rank reduction is necessary; it does not assert that a solution of this small system defines a full tableau.

The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ClockTwinReceipts.lean) checks the two-receiver separation and the four Hilbert inverses. The tableau chronology and polynomial interpolation arguments above are source-level.
