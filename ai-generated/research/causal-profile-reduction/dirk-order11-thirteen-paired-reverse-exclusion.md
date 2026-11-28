# The two-active-dirty-label face of DIRK11/13 is impossible

Under the explicit normalized hypotheses of the
[signed cubic census](dirk-order11-thirteen-signed-cubic-census.md), a
real 13-stage order-eleven DIRK tableau cannot have exactly two
distinct active cubic-dirty clocks. Thus the remaining active-clock
counts in that census are **0, 1, or 9**. The ordinary stage interval
**13–14** does not change. This supersedes the two-label midpoint and
chronological restrictions from the [older note](dirk-order11-thirteen-dirty-chronology.md):
those were necessary tests on a chart that is now empty.

The equality census gives a literal lower triangular \(A\), ordinary
weights \(\beta=b^{\mathsf T}\), stage clock \(c=A\mathbf1\), real
output order eleven, \(C(2)\), \(D(1),D(2)\), and the stated
grade-six surplus. In the two-label face there are exactly two
cancelling active dirty pairs: each pair has a common clock and
equal nonzero forward cubic defect and opposite nonzero weights.
There are two unweighted dirty singleton ghost rows, and seven
active clean physical rows at distinct numerical clocks including
the actual origin and terminal. A dirty label may coincide with
a clean numerical clock. No sign or clock-interval requirement is
added to this census.

## The reverse endpoint costs a dimension

In chronological reverse order, write \(N=A^\mathsf T\), interpreted
with the same reversal of rows and columns, and \(y=1-c\).
For \(P\in K[X]\), \(W(P)=b\,P(y)\) denotes pointwise multiplication
and \(I P(x)=\int_0^x P\) the scalar primitive. Use
\[
  U_0=\operatorname{Ann}E_6,\qquad
  Z=\{\ell\in\operatorname{Ann}E_5:\ell_T=0\}.
\]
The two physical pair contrasts span \(U_0\) by the census:
\(\operatorname{Ann}E_6=\operatorname{span}(\beta g,\beta Cg)\),
and evaluation at the two distinct active dirty labels separates
the two contrasts. Thus \(\dim U_0=2\). The terminal lies in
\(E_6\) as its unit coordinate, but not in \(E_5\). The dimensions
\(\dim E_5=9,\dim E_6=11\) give \(\dim Z=13-9-1=3\), with \(U_0\subset Z\).
All \(U_0\) vectors vanish at the clean rows, and \(N U_0\subset Z\)
because \(A E_5\subset E_6\) and the literal terminal column of \(A\)
is zero (including the terminal diagonal).

For any \(\deg P\le4\) the **genuine** reflected monomial primitive
error \(N W(P)-W(I P)\) lies in \(\operatorname{Ann}E_5\): the primitive
has grade at most five, which is paid against \(E_5\) by order
eleven. The error also has terminal coordinate zero: the terminal
column of the original \(A\) is zero, \(y_T=0\), and \(I P(0)=0\).
Thus it lies in \(Z\). This is a statement about actual weighted
rows with ghosts retained, not about whether the weighted transpose
is an RK order-eleven tableau.

## An inclusive cut gives two independent directions

Let \(u,v\) be the first two nonzero clean clocks in reverse physical
order. Both are active, nonzero and numerically distinct. Let
\[
       H(X)=X(X-u)(X-v).
\]
For \(Q\in{\cal P}_1\) put \(P=H Q\); this spends degree at most
four. Remove from \(W(P)\) its pointwise restriction \(W_{\rm d}(P)\)
to the four dirty *active* rows. This whole restriction belongs to
\(U_0\), even when the dirty and clean sets share clock values:
each pair's two contributions form its literal contrast by equal
clocks and opposite weights. The two ghosts carry weight zero.
The remainder \(W(P)-W_{\rm d}(P)\) has zero entries on **every**
physical row through the second chosen clean clock, including its
own row. Its support is clean, and \(H\) vanishes at the possible
clean clocks \(0,u,v\) throughout that reversed slice. Lower
triangularity of \(N\), with its diagonal retained, therefore gives
zero under \(N\) at both sampled clean rows.

Consequently the literal vectors
\[
  D_Q=N(W(P)-W_{\rm d}(P))-W(I P)
\]
lie in \(Z\), as the difference between the genuine primitive error
and \(N W_{\rm d}(P)\). At the two samples their entries are
\(-b_i I(HQ)(y_i)\). If \(D_Q\in U_0\) both entries vanish, and
both \(b_i\) are nonzero. Then \(I(HQ)\) has three roots \(0,u,v\)
and has derivative zero at all three because its derivative is
\(H Q\). A nonzero polynomial of degree at most five cannot have
these three distinct double roots. Thus \(Q=0\) and the two
directions are independent modulo \(U_0\). The resulting
\(\dim Z\ge2+2=4\) contradicts the terminal debit.

For an explicit scalar receipt, the two evaluations of \(I H\) and
\(I(XH)\) are
\[
       \left(\frac{u^3(2v-u)}{12},\
                       \frac{u^4(5v-3u)}{60}\right)
\]
and the same row with \(u,v\) interchanged. Their determinant is
\(u^3v^3(u-v)^3/120\). The quotient argument works over all
characteristic-zero fields given these rank and support premises;
the determinant itself uses only the displayed nonzero guards and
the indicated integer denominators. The signed support census
used to obtain those premises still has ordered-field inputs.

The reviewed adapter
[`DIRKOrderElevenThirteenPairedReverse.lean`](../../lean/RKCert/ReviewedNative/DIRKOrderElevenThirteenPairedReverse.lean)
implements the rank contradiction on actual rooted-tree spaces with
the `PairedReverseCut` mask, literal terminal shape and normalized
hypotheses explicit. The theorem `no_paired_reverse_cut` does not
assume individual nonzero weights away from the two samples.
The counted two-pair profile supplies that mask as explained above.
See the [typed audit](dirk-order11-thirteen-paired-reverse-audit.txt).
