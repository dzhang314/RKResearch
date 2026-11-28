# Two exact positive-width boxes fail the dormant-center quadratic

**Scope.** This strengthens the [quadratic reciprocal gate](ERK11-NONZERO-TEN-TWELVE-NONALIASED-CENTER-QUADRATIC.md) in the ordered all-live, half-clock, two-carrier order-eleven chart with both seventh boundaries new, \(q=10,n=12\), two full plateau pairs and sole dormant physical 9. Write \(a,d=1-b\) for the plateau labels and \(s=c_9\). The following closed three-parameter boxes contain no actual candidate:
\[
\begin{array}{c|c|c|c}
 &a& d&s\\ \hline
 1 &[19/100,21/100] &[39/100,41/100] &[71/100,37/50]\\
 2 &[39/200,41/200] &[79/200,81/200] &[7/10,3/4].
\end{array}
\]
In each box \(a,b>0\), \(a\ne d\), and \(s\) lies outside the four named endpoint/plateau labels. No separation of \(s\) from other active clocks, no centroid guard and no assumption about positivity of the individual stage weights is imposed. No unrestricted stage interval changes.

## 1. The discriminant can be cleared by a positive square

Use \(\mathcal A,\mathcal C\) for the true two bilinear rows of the quadratic gate, and \(J_0\ne0\) for the actual mixed primitive integral. Replace these rows by
\[
 \mathcal A^\sharp=J_0 a^5 b^5 \mathcal A,\qquad
 \mathcal C^\sharp=\mathcal C/J_0 .
\]
The second row is polynomial because all its displayed coefficients contain \(J_0\). For the first, the polynomial parts of the scaled evaluation rows are
\[
 \widetilde L_s=
       \frac{a^5\ell_s-30\mathscr P(s)\ell_a}{s(s-a)}
           +30u\ell_a,\qquad
 \widetilde R_s=
       \frac{b^5r_s^{\rm ev}-30\mathscr Q(s)r_d^{\rm ev}}{(1-s)(s-d)}
           +30v r_d^{\rm ev}.
\]
The two quotients are exact polynomial divisions. These are \(a^5 L_*, b^5R_*\), so the scaled reciprocal row is \(J_0[\widetilde L_s,\widetilde R_s]-a^5 b^5 uv\). All entries of both scaled rows are rational polynomials in \(a,b,s\).

Each coefficient of their eliminated quadratic \(E^\sharp(u)\) is \(a^5b^5\) times the original coefficient. Therefore the scaled discriminant is \(\Delta^\sharp=a^{10}b^{10}\Delta\). The multiplier is strictly positive over any ordered field with live widths, in particular in the two boxes. Thus it is enough to establish \(\Delta^\sharp<0\). The standalone replay constructs this polynomial exactly and checks degrees \((26,26,12)\) and support count 5607.

## 2. A coefficient bound over the entire box

Center the width variables at \(a=1/5,\ b=3/5\), and denote their deviations by \(A,B\). In box 1, \(|A|,|B|\le 1/100\); in box 2 they are at most \(1/200\). For clock interval \([l,r]\), form
\[
 (1+t)^{12}\Delta^\sharp\!\left(1/5+A,\,3/5+B,\,
                                     \frac{l+r t}{1+t}\right)
       =\sum_{k=0}^{12} f_k(A,B)t^k .
\]
Let \(m_k=f_k(0,0)\), and for width radius \(\varepsilon\) put
\[
 D_k=\sum_{i+j>0}|[A^iB^j]f_k|\,\varepsilon^{i+j}.
\]
The exact replay checks all thirteen inequalities \(m_k<0\) and \(D_k<-m_k\) per box, with the stronger checks \(D_k/(-m_k)<93/100\) for box 1 and \(<43/100\) for box 2. The triangle inequality in the ordered field gives \(f_k(A,B)\le m_k+D_k<0\) for **all widths** in the box. For \(t\ge0\) the homogeneous polynomial is strictly negative throughout \([l,r)\); its leading coefficient is also the value at \(s=r\), so the right endpoint is included. This proves negative discriminant over the whole box by exact rational arithmetic, not by interpolating numerical samples or continuity.

A true root \(u\) would instead give nonnegative discriminant, by \(\Delta^\sharp=(2E^\sharp_2u+E^\sharp_1)^2\). The companion core Lean formalizes the scalar clearing and completion identities. The ordered coefficient argument and physical tableau bridge are mathematical.

For deterministic replay with Python and python-flint 0.9.0:

    PYTHONDONTWRITEBYTECODE=1 python3 -B replay_erk11_nonaliased_center_width_boxes.py

The replay needs no external data or random search; one reference run took 0.857 seconds wall time.

Run the [standalone exact replay](erk11-nonaliased-center-width-boxes/replay_erk11_nonaliased_center_width_boxes.py). The [Lean scalar companion](../lean/RKCert/ReviewedNative/ERK11NonaliasedCenterBoxGate.lean) was checked on all four supported releases.
