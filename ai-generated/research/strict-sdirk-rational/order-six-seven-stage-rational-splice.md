# Seven rational strict SDIRK stages attain exact order six

Seven is the previously proved order-six stage floor in characteristic
zero. The rational tableau below attains it with exactly seven stages
and has exact order six. Its five nonzero output weights are positive.
The construction uses the fixed five-site Boole rule, the two-row
interpolation core from the order-five splice, and one additional
linear compatibility. There is no search over tableau coefficients.

## Literal tableau

The common diagonal is \(1/4\); entries above the lower triangle are
zero.

| Row | Entries |
|---:|---|
| 1 | \(1/4\) |
| 2 | \(-1/2,\,1/4\) |
| 3 | \(-1/8,\,-1/8,\,1/4\) |
| 4 | \(31/24,\,7/24,\,-5/6,\,1/4\) |
| 5 | \(7/48,\,1/48,\,11/96,\,-1/32,\,1/4\) |
| 6 | \(119/768,\,53/768,\,-155/1536,\,9/512,\,-9/64,\,1/4\) |
| 7 | \(-119/256,\,-29/256,\,207/512,\,-31/512,\,15/64,\,1/2,\,1/4\) |

The output weights and physical clocks are
\[
\mathbf b\coloneqq(0,0,7/90,7/90,2/15,16/45,16/45),\qquad
\mathbf c\coloneqq(1/4,-1/4,0,1,1/2,1/4,3/4).
\]
The [exact replay](check-order-six-seven-stage-splice.py) derives this
table and then runs the rooted-tree recursion on the literal table.
It passes all \(1+1+2+4+9+20=37\) trees through order six and fails
all 48 order-seven conditions. The order-seven tall weight is
\(7/40960\), not \(1/5040\). The checker also verifies \(D(1)\),
the exact grade-space ranks \(1,2,4,6,7,7\), and that
\[
A\mathbf c-\mathbf c^{\odot2}/2=(1/32,-7/32,0,0,0,0,0).
\]
No stability property is claimed.

## Exact order-six gate for the two-row interpolation splice

Use the [two-donor order-five splice](order-five-six-stage-splice.md).
The rational common nonzero diagonal is \(\gamma\); the second core
clock is \(\eta\ne\gamma\). Let the two core rows be
\[
G\coloneqq\begin{pmatrix}\gamma&0\\\eta-\gamma&\gamma\end{pmatrix}
\]
with zero weights and linear interpolation map \(\Pi\) at
\(x=\gamma,\eta\). The suffix clocks \(x_i\) and nonzero weights
\(w_i\) satisfy degree-five quadrature; let \(y_i\coloneqq1-x_i\).
Work in the reflected chronological order, so the lower triangular
weighted-dual block \(L\) has fixed diagonal \(\gamma\) and
\(L\mathbf1=\mathbf y\). Reverse the weighted transpose back to the
primal suffix block \(T\), and use \(K\coloneqq(EJ-TE)\Pi\) for the
core-to-suffix coupling, where \(E\) is evaluation and \(J\) is
polynomial integration from zero. The suffix is exact pointwise
through stage grade two and \(D(1)\) holds on the full tableau.

Let the polynomial space of degree at most three be \(\mathcal P_3\);
write its suffix evaluation implicitly in weighted pairings.
Define the grade-two core residual space and the two reflected
defects by
\[
\begin{gathered}
N(x)\coloneqq(x-\gamma)(x-\eta),\qquad
M(x)\coloneqq x^2/2-2\gamma x+\gamma^2,\qquad
\mathcal F_2\coloneqq\operatorname{span}(N,M),\\
\boldsymbol\delta\coloneqq L\mathbf y-\mathbf y^{\odot2}/2,\qquad
\boldsymbol\varepsilon\coloneqq
L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3 .
\end{gathered}
\]
Within this rational splice chart, order six is equivalent to
\[
\boldsymbol\delta\perp_w\mathcal P_3,\qquad
\boldsymbol\varepsilon\perp_w\mathcal F_2,\qquad
L\boldsymbol\delta\perp_w\mathcal F_2. \tag{1}
\]

### Necessity and the first repeated-site obstruction

For the full tableau let \(Y\) be diagonal multiplication by
\(1-\mathbf c\). The paid reverse rows
\(\mathbf b^\mathsf T Y A-\mathbf b^\mathsf T Y^2/2\) and
\(\mathbf b^\mathsf T Y^2 A-\mathbf b^\mathsf T Y^3/3\)
annihilate the actual tree columns through grades three and two,
respectively. This is the formal polynomial integration-by-parts
identity with the stated paid degrees, and does not divide by core
weights. On a pair of core/suffix vectors \((\mathbf u,\mathbf v)\)
these rows are exactly the weighted pairings of
\(\mathbf v-E\Pi\mathbf u\) with respectively
\(\boldsymbol\delta,\boldsymbol\varepsilon\).
For example, the core part of the first row is
\(\mathbf w^\mathsf T Y K=-\mathbf w^\mathsf T
\operatorname{diag}(\boldsymbol\delta)E\Pi\):
use \(\int_0^1 yJf=\int_0^1(y^2/2)f\) on the linear interpolation
profiles. The cubic relation uses the identical identity for \(y^2\).

The two grade-two trees have exact suffix values and give the
\(\boldsymbol\delta\) and \(\boldsymbol\varepsilon\) pairings with \(N,M\).
A grade-three bush and the mixed tree \(C A\mathbf c\) have exact suffix
values as well; the latter uses the exact suffix quadratic primitive.
Their residuals have cubic leading terms \(x^3\) and \(x^3/2\).
The linear difference of these profiles, and the linear profile
\(N-2M\), are linearly independent over \(\mathbb Q\).
Indeed, with \(u\coloneqq\eta/\gamma\), their value at \(\gamma\)
is respectively \(\gamma^3\) and \(\gamma^2\); at \(\eta\) the
values are respectively
\(\gamma^3(4u^2-2u-u^3)\) and
\(\gamma^2(-u^2+4u-2)\).
After dividing by the indicated powers of \(\gamma\), the difference
of the second values is \(-(u-1)(u^2-4u+2)\). The first factor is the
excluded coincident core, and the other has no rational root.
These two linears, a quadratic profile and a cubic profile span
\(\mathcal P_3\). This proves the first condition of (1) from
actual paid trees, not from independently imposed word tests.

The two remaining grade-three trees are unary extensions of the
grade-two trees. Their actual suffix errors are respectively
\((TE-EJ)N\) and \((TE-EJ)M\); their polynomial residuals have degree
at most three. Hence the first paid reverse row forces
\(\langle\boldsymbol\delta,(TE-EJ)f\rangle_w=0\) for
\(f\in\mathcal F_2\). Since \(Jf\) has degree at most three, this
is exactly the \(L\boldsymbol\delta\) condition. The
\(\boldsymbol\varepsilon\) condition was supplied by the second
paid reverse row above.

In particular the chart cannot use five active rows at just four
distinct rational quadrature sites. The four aggregate weights
are nonzero by the rational four-site lower bound. The first
condition of (1) kills the aggregate of \(w_i\delta_i\) at each
of these sites by cubic interpolation. But the first two reflected
errors are forced to be
\(\delta_1=\gamma^2/2\) and
\(\delta_2=2\gamma y_2-\gamma^2-y_2^2/2\), both nonzero over the
rationals. They would have to be the sole repeated pair. Equal
\(y_1=y_2=\gamma\) forces equal errors, incompatible with their
nonzero aggregate weight. This obstruction is for the specified
splice, not for arbitrary seven-stage rational methods.

### Sufficiency with precisely these tests

For a tree \(t\) of grade \(|t|-1\), its scalar profile is
\(f_t(x)\coloneqq |t|x^{|t|-1}/t!\). On the suffix the exact unary
error recursion is
\[
\boldsymbol e_{[t]}=T\boldsymbol e_t+(TE-EJ)\rho_t,\qquad
\rho_t\coloneqq f_t-\Pi\boldsymbol\Phi_t(G).
\]
The first source is a grade-two residual followed by a unary step,
so it appears at stage grade three. Through grade five no root can
multiply two erroneous primitive factors: those cost at least six.
Thus output errors are sums of tests
\(\langle\mathbf1,B(TE-EJ)\rho_t\rangle_w\), with words \(B\) in
\(T,C\), where \(C\) is the suffix clock \(x\). At word lengths
zero, one, two the residual polynomial has degree at most
four, three, two respectively. At length two it is in \(\mathcal F_2\).

At length zero \(L\mathbf1=\mathbf y\) and exact quadrature kill the
source. At length one the two reverse errors are respectively
\(\boldsymbol\delta\) and \(-\boldsymbol\delta\). At length two, let
\(\mathbf h\) be the reverse word acting on \(\mathbf1\) and let
\(h_0\) be its formal scalar version. The differences are exactly:

| \(B\) | \(\mathbf h-Eh_0\) | \(L\mathbf h-EJ^*h_0\) |
|---|---|---|
| \(T^2\) | \(\boldsymbol\delta\) | \(\boldsymbol\varepsilon/2+L\boldsymbol\delta\) |
| \(TC\) | \(0\) | \(\boldsymbol\delta-\boldsymbol\varepsilon\) |
| \(CT\) | \(-\boldsymbol\delta\) | \(\boldsymbol\delta-\boldsymbol\varepsilon/2-L\boldsymbol\delta\) |
| \(C^2\) | \(0\) | \(\boldsymbol\varepsilon-2\boldsymbol\delta\) |

Here \(J^*g(x)\coloneqq\int_x^1g(t)\,dt\). The exact quadrature
cancels the formal scalar pairing
\(\langle EJ^*h_0,E\rho_t\rangle_w-\langle Eh_0,EJ\rho_t\rangle_w\)
through degree five. The middle column is paired with the cubic
\(J\rho_t\), and the last column with \(\rho_t\in\mathcal F_2\);
both vanish by (1). All actual rooted-tree output errors therefore
vanish. This is an exact equivalence for the chart, not a substitute
for direct replay of the displayed tableau.

## The shared-donor solve, with no nonlinear search

Use reflected chronology
\[
\gamma=1/4,\quad
\mathbf y\coloneqq(1/4,3/4,1/2,0,1),\qquad
\mathbf w\coloneqq(32,32,12,7,7)/90.
\]
This is just the fixed Boole rule. For five distinct clocks the
annihilator of cubic samples has weighted values proportional
to the reciprocal nodal derivatives. The first two clocks are
symmetric and satisfy \(y_2=3\gamma\); their barycentric weights
are equal and the two forced reflected defects both equal \(1/32\).
Thus this fixed rule already gives the right two-row seed,
\[
\boldsymbol\delta\coloneqq(1/32,1/32,-1/8,-1/28,-1/28).
\]
Fix the row sums and \(L\mathbf y\) using the first two donors
wherever possible. The first adjustable row, row four, can vary
only along
\[
\mathbf p_3\coloneqq(-1/2,-1/2,1,0,0).
\]
Row five has this direction and
\(\mathbf p_4\coloneqq(-3/2,1/2,0,1,0)\).
They preserve both already-paid actions. Their effects on
the two remaining error channels are the columns of
\[
\begin{pmatrix}
-1/16&3/16\\
-5/32&-15/224
\end{pmatrix}.
\]
The second effect is \(5/2\) times the first at row four;
at row five the two effects are independent.

The two test polynomials can be written \(M,P_\eta\), with
\[
P_\eta(x)\coloneqq N(x)-2M(x)=(3\gamma-\eta)x+\gamma(\eta-2\gamma).
\]
Rows four and five are at \(x=1,0\). Once their two sample vectors
are independent, the desired correction in each channel is a
two-equation linear solve. At row four the two desired changes
must be in ratio \(5/2\). Eliminate row five by taking the determinant
against its sample vector. The resulting compatibility is affine
in \(\eta\), since only the second test polynomial varies. On
the baseline rows its values at \(\eta=0,1\) are respectively
\(-1/18432,-5/18432\). Hence \(\eta=-1/4\).
The resulting receiver determinant is \(-1/16\). The row four
coefficient of \(\mathbf p_3\) is \(-3/56\); in row five the
coefficients of \(\mathbf p_3,\mathbf p_4\) are \(11/56,-5/6\).
Thus
\[
L\coloneqq\begin{pmatrix}
1/4&0&0&0&0\\
1/2&1/4&0&0&0\\
5/8&-3/8&1/4&0&0\\
-31/112&9/112&-3/56&1/4&0\\
207/112&-155/336&11/56&-5/6&1/4
\end{pmatrix}.
\]
All three conditions of (1) now hold, and the weighted transpose and
interpolation formula give the literal tableau at the top.

Run `python3 check-order-six-seven-stage-splice.py` for the exact
standard-library replay. The `seven-stage-order-six-numerators.json`
payload uses \(A\)-denominator 1536 and weight denominator 90 for
the reviewed finite scaled-tree checker. No Lean compiler was run
for this source receipt.

## Lean replay

The exact rational construction and both minimum-stage statements use
the reviewed HasOrder predicate. The two modules,
RationalStrictSDIRKSevenStageSixUpper and RationalStrictSDIRKOrderSixMinimum,
compiled and passed an independent kernel replay on Lean 4.36.0. Both
typed audits list only standard axioms.
