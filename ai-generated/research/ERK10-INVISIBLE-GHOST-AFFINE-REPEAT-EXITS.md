# The affine ten-label repeat and nine-label triple are impossible

Use the scope and notation of the
[unbalanced affine closure](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md)
over any characteristic-zero field: sole invisible ghost at physical
2, original \(f_4=4\), genuine reduced reverse quadratic \(u\),
nonzero pooled \(bu\), and \(r_I=L(C)u\) with genuinely affine
\(L\). This note excludes the **ten-label one-pair** remainder,
including a barycentric pole at the actual repeated clock.
It also excludes the **nine-label off-root triple** by a true
pure grade-six rank/terminal contradiction. Together the two
notes exhaust the stated affine, nonzero-pooled, rank-four
sole-invisible chart, not the other ERK10 equality branches.

## 1. Ten labels with one repeated physical pair

There are eleven active rows and only the two live endpoints are
dormant. The unique pair lies at \(w\). As in the main note,
\(D\) is the monic ten-label hull,
\(\nu=P/D'\), \(\mu=Q/D'\) for pooled first and second amplitudes,
\(\deg P\le1,\deg Q\le3\), and \(\tau\) is the pooled
third moment. The three paid cubic tests are
\[
      \sum L^2\tau=0,\qquad \sum X L^2\tau=0,\qquad
      \sum L\tau=0 .                                         \tag{1}
\]

First assume \(P(w)\ne0\); all active labels now have
nonzero \(\nu\), since the other labels are singletons.
Write \(G=Q/P\) on the labels and \(V=\tau_w-\nu_w G(w)^2\).
The cubic comparison is exact at every singleton.
If \(P\) is constant, the polynomial \(Q^2L^2/P\) has
degree at most eight, so the first test in (1) gives
\(L(w)^2 V=0\). Consequently the second test is just the
degree-nine polynomial comparison and forces \(\deg Q\le2\)
by its nonzero-leading-coefficient criterion.

If \(P\) is nonconstant with root \(\xi\), then \(\xi\ne w\)
and there is no singular active clock. The polynomial parts of
\(Q^2L^2/P\) and \(XQ^2L^2/P\) lie below degree nine.
Writing \(Z\) for the candidate residue of \(Q^2L^2/(P D)\)
at \(\xi\), the first two tests are precisely
\[
          L(w)^2 V-Z=0,\qquad w L(w)^2 V-\xi Z=0.
\]
Their distinct clock coefficients force \(Z=L(w)^2 V=0\).
The residue formula gives \(P\mid Q L\).

In either subcase \(R=LQ/P\) is a polynomial of degree at most
three. If \(L(w)\ne0\), then \(V=0\) and the ordinary two-point
variance identity with weights \(b_i u_i\) makes both amplitudes
at \(w\) equal to \(G(w)\). If \(L(w)=0\), then \(R(w)=0=r_i\)
on both repeated rows regardless of their amplitudes. Thus \(R\)
really describes \(r\) on every active row. The anchored Gram
at the only two dormant clocks 0 and 1 excludes this.

Now assume \(P(w)=0\), so \(P=\kappa(X-w)\) with \(\kappa\ne0\).
Subtract \(w\) times the first equation in (1) from the second.
The exceptional pair's contribution vanishes. At every singleton
the result has cancelled its \(X-w\) denominator, hence yields
\[
                \sum_{x\ne w}\frac{Q(x)^2L(x)^2}{D'(x)}=0 .
\]
The numerator has degree at most eight. Its Lagrange sum
over **all** ten labels is zero, hence the missed value
\(Q(w)^2 L(w)^2/D'(w)\) is zero. If \(Q(w)\ne0\), then
\(L(w)=0\) so \(L=\lambda(X-w)\), \(\lambda\ne0\).
Use the one-factor test in (1): the pair contributes zero and at
the other labels the factor \(L\) cancels \(P\). Thus the same
missing-value argument on \(Q^2\) forces \(Q(w)=0\).
This proves \(Q(w)=0\) in every case.

Now \(Q/P\) is a polynomial \(G\) of degree at most two,
giving \(u_i\) on every singleton. At the pair both
\(\nu_w=\mu_w=0\); the two nonzero amplitudes are equal
and the ordinary weights are opposite by the two-moment
identity. Thus their ordinary scalar sums vanish at \(w\)
even if the common value is not \(G(w)\).
The \(bu\) moments transfer to an exact \(G\)-weighted
quadrature supported only at the two dormant endpoints.
The anchored nonsingular Gram forbids nonzero \(G\).
This finishes ten labels without dividing by a value at the
physical repeated clock before checking whether it is zero.

## 2. Exact anchors and first intra-triple tap at nine labels

For the surviving nine-label case, write \(w\) for the
single off-root triple. The eight other active rows are
singletons, and the only dormant live rows are physical 1
and 14. The barycentric \(P\) is constant and the model
\(G=Q/P\) has degree at most two. Set \(R=LG\), so
\(r=R(c)\) at the eight singletons. At \(w\) the paid
variance test, with \(L(w)\ne0\), gives
\(\mu_w=\nu_w G(w)\), \(\tau_w=\nu_w G(w)^2\).
The ordinary scalar quadrature with \(R\) now has at most
the three support clocks \(0,w,1\): away from the triple
its active contribution is exactly \(r\), whose seven clock
moments are zero. If \(w\) is an endpoint, or if the triple
correction has zero weighted mass, only two sites remain
and the anchored Gram contradicts \(R\ne0\).
Therefore \(w\) is internal, the correction mass is
nonzero, and \((X-w)R\) is proportional to \(L_4\)
by the same anchored quartic calculation. In particular
\(R(w)\ne0\), \(G(w)\ne0\), and the distinct root of \(L\)
is a second interior Lobatto root.

Normalize \(R\) to \(L_4/(X-w)\), scaling the entire
genuine grade-three mask \(R(c)-r-R(c_2)e_2\) by the
same nonzero factor. Call the normalized mask \(T\).
It is supported only at the endpoints and the triple.
The numerical vector
\[
                              K=(C-w)T=e_1+e_{14}
\]
is genuine grade four with model \(L_4\). Consequently
\(CK=e_{14}\) and \((1-C)K=e_1\) are genuine grade-five
pairs, with scalar means both \(1/30\). Thus
\[
        b_1=b_{14}=1/30,\qquad A_{14,1}=1/15 .
\]
The last follows by testing the true grade-nine product
\(K(AK)\): its numerical mean is \(b_{14} A_{14,1}\)
since \(Ae_{14}=0\), and its model mean is
\(\int L_4 J L_4=\tfrac12(\int L_4)^2=1/450\).

At the three actual physical rows \(i_1<i_2<i_3\) at \(w\),
write \(p_a=T_{i_a}/R(w)=1-u_{i_a}/G(w)\).
Every \(p_a\ne1\), since the rows are active, and variance
gives
\[
         \sum_a b_{i_a}p_a=\sum_a b_{i_a}p_a^2
           =\sum_a b_{i_a}p_a^3=m\ne0 .
\]
Indeed the two paid grouped equations on \(p\) are
\(\sum b_{i_a}p_a(1-p_a)=
  \sum b_{i_a}p_a^2(1-p_a)=0\).
If there were at most two distinct nonzero \(p\)-values,
these two amplitude tests make each such group's ordinary
weight zero (as \(p\ne0,1\)), contradicting \(m\ne0\).
Therefore all three are distinct and nonzero.

Projection gives \(F_5|_I=u\,\mathcal P_{\le3}(c_I)\):
it contains these four independent clock powers by applying
\(C\) to the known \(F_4|_I\); the fifth pure dimension
is \(e_2\). The genuine \(A(CT)\) is grade five, so at
the common clock \(w\) its three numerical values are an
affine function of \(p_a\). Its first is zero by strictness
since \(CT\) vanishes at the old origin and on every
earlier active singleton. Thus
\[
                       (A(CT))_{i_a}=\gamma(p_a-p_1).
\]
The exact middle-seam scalar in the main note is nonzero
at the Lobatto root \(w\). The weighted product
\(A(CT)(1-C)T\) now has only triple contributions and equals
\(\gamma(1-w)R(w)\,m(1-p_1)\).
Hence \(\gamma\ne0\). At the second chronological triple
row there is only a single contributing root read in \(CT\):
\[
                A_{i_2,i_1}\, w R(w) p_1
                         =\gamma(p_2-p_1)\ne0 .
\]
In particular the first intra-triple tap would be live.
An independent rank/terminal contradiction now excludes the chart.

## 3. The triple produces one pure grade-six direction too many

The exact original \(f_6=7\) rank comes from the higher alias
calculation of the
[fourteen-stage equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md).
We account for all seven directions.

First, \(F_4|_I=W_3=u\mathcal P_{\le2}(c_I)\) was earned
using \(f_4=4\), the one-dimensional ghost kernel \(Ke_2\),
and duality with \(E_5\). In particular the **three separate**
directions \(u,Cu,C^2u\) on live coordinates have actual old
grade-four pure lifts. Subtract their value at the ghost
times \(e_2\) to choose each lift zero there; the subtraction
is within grade four. Thus the chosen whole old extension of
\(u\), zero at the ghost, also has the pure profiles \(Cu,C^2u\)
already at grade four. Multiply the last of those **paid**
lifts by \(C,C^2\) to put \(C^3u,C^4u\) in grades five, six.
This is not an inference from an arbitrary function called
\(u\) on the live set. Together with \(e_2\), these are six
independent original grade-six pure directions: distinct
active clocks yield independence of the five polynomial
coefficients, and the ghost coordinate detects \(e_2\).

The seventh direction is the literal Hadamard difference
\[
                            V=T^2-R(c)T.
\]
Both terms cost at most grade six: \(T\) is a genuine
grade-three pair with model \(R\), and \(R(c)\) is an
ordinary clock-polynomial pair of degree three. Their
models both equal \(R^2\), so \(V\) is actual **pure**
grade six. At the endpoints \(T=R(c)\), at the ghost and
the eight active singleton rows \(T=0\); hence \(V\) is
supported only on the triple at \(w\). There
\[
                     V_{i_a}=R(w)^2p_a(p_a-1)\ne0
\]
because \(R(w)\ne0\) and \(p_a\ne0,1\).
In the six-direction span any vector with that support
would have zero ghost coefficient, and its \(u\)-polynomial
of degree at most four would vanish on the **eight distinct
active singleton clocks** (each \(u_i\ne0\)). It must be
identically zero, contrary to \(V\ne0\).
We have used all seven pure directions, and every one of
them vanishes at physical 14. In exact pointwise form,
\[
       v\in F_6\ \Longrightarrow\
       v_i=\alpha(e_2)_i+u_i\,S(c_i)+\beta V_i
       \ \text{for all physical }i,\quad \deg S\le4,
       \quad v_{14}=0,
\]
where \(u\) now denotes the just-paid ghost-zero lift in
the numerical formula.

But the genuinely grade-five endpoint indicator
\(CK=e_{14}\) has model \(X L_4(X)\).
Strict lower triangularity gives \(Ae_{14}=0\) **as a
numerical column**; its grade-six pair has formal model
\(J[X L_4](X)\), whose value at 1 is
\[
               \int_0^1 X L_4(X)\,dX=1/30\ne0.
\]
Subtract its ordinary clock-polynomial model (of degree six)
from this zero numerical column. This creates an actual
pure grade-six vector with value \(-1/30\) at physical 14,
contradicting the complete seven-dimensional span.
The contradiction closes the last triple without a fourth
amplitude moment or higher reduced reverse order.

[ERK10InvisibleAffineRepeatGate.lean](../lean/RKCert/ReviewedNative/ERK10InvisibleAffineRepeatGate.lean)
checks the residue/variance separation, missed-value cancellation,
paired amplitude, first-tap and grade-six terminal arithmetic. The weighted and
chronological reductions are the audited mathematics above.
