# The 28-row forward chart for order thirteen

## 1. An existing order-seven contrast in the order-nine seed

The [paid 16-row order-nine tableau](../erk-nine-moment-splice/README.md) contains the physically merged
non-donor stages at clocks \(1/4,3/4\). Each has the full literal
prefix incoming row \(I_x\Pi_4\), with no suffix inputs, in the
order-nine construction. Here \(\Pi_4\) is that construction's
degree-four forward projection and \(I_x\) denotes integration
from 0 to \(x\).

For any six-vertex source tree \(t\), its polynomial discrepancy
\(\rho_t\) is zero at \(0,1,1/2\) and has zero integral.
The midpoint assertion uses the already proved literal midpoint
merge: the old midpoint read equals \(I_{1/2}\Pi_4\), and
\(\Pi_4\) is exact through tree order five. Consequently the
midpoint derivative is exact through tree order six. In the
variable \(u=2x-1\), the discrepancy is of the form
\[
 (1-u^2)u(Au^2+Bu+C).
\]
Its zero integral forces \(B=0\), since the centered even moment
\(\int_0^1(1-u^2)u^2\,dx=2/15\) is a unit. Thus \(\rho_t\)
is odd about \(1/2\). Its primitive from zero takes equal values
at \(1/4\) and \(3/4\).

In a seven-vertex tree, the first possible primitive error arises
only from a sole child of size six. At either of the two non-donor
stages that error is the primitive of the same \(\rho_t\) up to
sign. Their difference is therefore exact, including on
seven-vertex trees. In other words, the difference of their
physical coordinate rows realizes \(E_{1/4}-E_{3/4}\) through
tree order seven, at no new stage cost.

## 2. The complete order-13 forward part in 28 actual rows

Use the 16-row order-nine seed and append its literal endpoint.
The endpoint evaluations \(E_0,E_1\), with moments
\(I_1,I_1^x,I_1^{x^2},I_1^{x^3}\), are the paid degree-five
chart from the [order-twelve construction](../erk-eleven-twelve-moment-splice/README.md). They supply order-six
derivative information. Append its primitive row at \(1/2\).

The next chart, of degree at most six, uses
\[
 E_0,\ E_1,\ I_1,\ I_1^x,\ I_1^{x^2},\
 (E_{1/4}-E_{3/4}),\ E_{1/2}.
\]
The first five rows have a two-dimensional kernel with basis
\[
 \begin{split}
  (1-u^2)(u^3-3u/7),\\
  (1-u^2)(u^4-2u^2/3+1/21).
 \end{split}
\]
Their moment orthogonality follows from integrating the displayed
monomials. The coefficient basis is integral over the paid ring:
the first five rows are already a beta-Hankel unit system on
polynomials of degree at most four, and the displayed two
polynomials are monic up to sign in the two remaining degrees
in the paid variable \(u\). The contrast has response \(15/112\)
on the first and 0 on the second. Midpoint evaluation has
responses \(0,1/21\). These two unit pivots complete the chart.

Append the four local rows at \(1/12,1/4,1/3,1/2\), now using
this order-seven chart. The next degree-seven chart uses these
four evaluations, the endpoints, and \(I_1,I_1^x\). Its determinant
is the same scalar determinant as in the order-twelve prefix,
\(275/95865912019648512\), hence a paid unit. It is independent
of the particulars of the preceding raw matrix.

Append six local rows at \(-1/2,1/4,1/3,2/3,3/4,3/2\).
The final degree-eight chart uses those six evaluations, \(E_0,E_1\),
and \(I_1\). Let \(Q_8\) be the monic polynomial with roots these
eight evaluation sites. Every pairwise difference is paid.
The previously proved nine-node quadrature, which adds the
midpoint to precisely those eight sites, gives
\[
     \int_0^1 Q_8(x)\,dx=(6/7)Q_8(1/2).
\]
This is a unit, so the final scalar pivot is paid. The count
is \(16+1+1+4+6=28\), with \(E_0,E_1\) and literal \(I_1\)
pins. An endpoint generated from the order-nine seed is exact
enough for the lower-seed four-donor splice at order thirteen.
