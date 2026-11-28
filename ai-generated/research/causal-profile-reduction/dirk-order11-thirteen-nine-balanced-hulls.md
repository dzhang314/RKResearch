# Scalar hull and middle-Volterra reduction for balanced DIRK11/13

This is an exact **necessary-system reduction**, not a new width bound.
It applies to the [four surviving nine-label chronologies](../dirk11-thirteen-nine-five-side/README.md),
conditional on the same normalized actual-order-eleven rank and support
inputs. It allows repeated numerical clocks across clean and dirty
colors, arbitrary signs, and exterior clocks. The statement uses
genuine forward and backward paid rows, not order of a transposed
RK tableau.

Write the actual clean stages in physical order as \(0,e,f,1\);
let \(U\) be the cubic defect profile on the nine distinct dirty
clocks and \(h=U(c)-g\). The virtual rule on the four clean sites
and three roots \(\rho\) of \(U\) has exact degree ten and nonzero
weights \(m_\rho\). Write \(L,W,R\) for the three monic actual dirty
nodal products before \(e\), between \(e,f\), and after \(f\);
their degrees are \(a,m,d\), and \(V=LWR\). No factor in these
products vanishes at a root of \(U\).
All statements modulo \(U\) use evaluation at its three simple
roots, so polynomial representatives of degree at most two are
unique. The scale \(\kappa\ne0\) of the nine dirty barycentric
weights gives
\[
                  L(\rho) W(\rho) R(\rho)
                                 =-\frac{\kappa}{m_\rho U'(\rho)} .
\]

## Factor the literal polynomials from their cuts

Put \(A_0=I(XU)\), \(A_1=I(X^2U)\),
\(B_0=I^\leftarrow((1-X)U)\), \(B_1=I^\leftarrow(X(1-X)U)\),
and \(G^\leftarrow(X)=G(1-X)\) with \(G\) the fixed degree-six
virtual pure mode from the five-side proof. Define
\[
\begin{split}
 H_L &= A_1-eA_0
       - \frac{A_1(e)-eA_0(e)}{G(e)} G,\\
 H_R &= B_1-fB_0
       -\frac{B_1(f)-fB_0(f)}{G^\leftarrow(f)}G^\leftarrow .
\end{split}
\]
The denominators are checked nonzero by the seven-site rule:
\(G\) and its mirror span the endpoint-zero six-point moment
kernels, whose generating coordinates are all nonzero.

The true forward derivative of \(Ch\) has a degree-at-most-five
dirty trace, vanishes at all \(a\) early dirties, and equals
\(A_0\) at the virtual roots. The derivative of \(C(C-e)h\)
has degree at most six and vanishes at all early and middle
dirties, since its only possible input support is \(f,1\).
Its virtual correction is determined by its actual zero at \(e\),
so its virtual value is \(H_L\). The exact mirror statements
use the corresponding genuine weighted rows
\(b(1-c)h\) and \(b(1-c)(c-f)h\) after multiplication by \(A\)
and division by the nonzero dirty \(b_i\).
Their degree bounds are at most five and six by the compensated
annihilator arguments. The respective literal polynomials are
\[
 P_L=L\ell_L,\quad Q_L=LWk_L,\qquad
 P_R=R\ell_R,\quad Q_R=RWk_R
\]
with all four traces nonzero and
\[
 \deg\ell_L\le5-a,\quad\deg\ell_R\le5-d,\qquad
 \deg k_L\le d-3,\quad \deg k_R\le a-3 .
\]
The nonzero reports are the already paid Hermite clean-support
separation, not a genericity assumption. In particular
\[
 L\ell_L=A_0,\quad LWk_L=H_L,\quad
 R\ell_R=B_0,\quad RWk_R=H_R \pmod U.
\]
These four congruences have at most three scalar coefficients each.
They require no division by the prospective \(\ell_L,\ell_R\).

There is also a useful explanation of redundant first-clean
quadrature tests. Let \(\omega_\rho^f\) denote the virtual
five-node ordinary integration taps for \(\int_f^1\), at the
sites \(f,1,\rho_1,\rho_2,\rho_3\). Then identically
\[
 m_\rho H_L(\rho)=b_f f(f-e)U(f)\,\omega_\rho^f .
\]
Indeed \(A(C(C-e)h)=f(f-e)U(f)A e_f\): the literal terminal
column is zero. Pairing with any degree-four clock polynomial,
the exact backward primitive at \(f\) gives its right-hand
integral. The virtual grade-six trace transfers the same
five moments to the five possible sites \(f,1,\rho\); uniqueness
is just interpolation on those sites. The reversed identity
uses the five-node integration rule for \(\int_0^e\).
Thus these local virtual mass ratios by themselves do not give
an independent obstruction.

## A small three-cubic pencil when \((a,m,d)=(3,3,3)\)

Both \(k_L,k_R\) are nonzero constants. Thus \(H_L,H_R\)
are nonzero at all roots of \(U\), since \(L,W,R\) are.
Let \(M(\rho)=m_\rho U'(\rho)\). Multiplying the congruences
and using the global barycentric identity gives
\[
 \begin{split}
 W(\rho)&=-M(\rho)H_L(\rho)H_R(\rho)/(\kappa k_L k_R),\\
 L(\rho)&=-\kappa k_R/[M(\rho)H_R(\rho)],\\
 R(\rho)&=-\kappa k_L/[M(\rho)H_L(\rho)].
 \end{split}
\]
Every quantity being divided by is nonzero in this chart.
Each of the three monic cubics belongs to a one-parameter pencil
\(U_{\rm mon}+tQ_2\), with a fixed degree-at-most-two remainder
direction explicitly obtained by interpolation at the virtual
roots. The scales are shown above, so the true barycentric
normalization can be retained. In the asymmetric cases
\((3,2,4)\) and \((4,2,3)\), the same argument fixes the
three-dirty-side monic cubic in the corresponding pencil;
the other endpoint-separated quotient is affine, not constant.

## A denominator-safe shared diagonal when \((a,m,d)=(4,1,4)\)

Let \(z\) be the single physical middle dirty clock, so \(W=X-z\).
Both \(\ell\)'s and both \(k\)'s have degree at most one.
Let \(d_e=A_{ee}\) and \(d_f=A_{ff}\); the pure clean block gives
\[
 d_e=\frac{A_0(e)}{eU(e)},\qquad
 d_f=\frac{B_0(f)}{(1-f)U(f)} .
\]
The forward Volterra image of \(Ch\) and the mirror of
\((1-C)h\) have degree-at-most-six dirty traces and vanish on
the four dirties of the respective first block. Write them as
\(L\eta_L\) and \(R\eta_R\), with degree-at-most-two \(\eta\)'s.
The literal first pivots and virtual kernels give the extra congruences
\[
 \begin{split}
 L\eta_L &= -d_e^2 eU(e)\,G/G(e),\\
 R\eta_R &= -d_f^2(1-f)U(f)\,G^\leftarrow/G^\leftarrow(f)
 \pmod U .
 \end{split}
\]
In particular these formulas remain valid at a zero clean
diagonal. They use the backward row normalized by \(b_i\)
only on its live coordinates.

The single middle stage gives an additional equation off the
virtual cubic. Let \(d_z\) be its unmodified actual diagonal.
Since the only earlier nonzero source of \(Ch\) is at \(e\),
the middle Volterra read is
\[
 \eta_L(z)=\ell_L(z)(z-e-d_e-d_z).
\]
For the exact mirrored clock \(1-c\), the same calculation gives
\[
 \eta_R(z)=\ell_R(z)(f-z-d_f-d_z).
\]
For example the first formula follows by noting
\(A(Ch)(z)=A_{z,e} eU(e)\),
\(AC(Ch)(z)=e A(Ch)(z)\) and
\(A^2(Ch)(z)=(d_e+d_z)A(Ch)(z)\), then cancelling \(L(z)\ne0\).
For the second formula the same weighted adjoint computation
cancels \(R(z)\ne0\). No order or extra tree stage on that
adjoint is introduced.

One can eliminate the true middle diagonal by subtracting the
two equations after cross multiplication:
\[
 \ell_R(z)\eta_L(z)-\ell_L(z)\eta_R(z)
      =(2z-e-f+d_f-d_e)\ell_L(z)\ell_R(z).
\]
Keep the separate individual equations if a multiplier vanishes:
they additionally force the corresponding \(\eta(z)=0\).
No division by a possibly zero \(\ell_L(z)\) or
\(\ell_R(z)\) is needed. The spectrum \(L,W,R\) and the
isolated middle coordinate here are necessary polynomial data,
not a constructed tableau. Whatever survives these scalar tests
still has to meet the chronological raw prefix and suffix taps.
