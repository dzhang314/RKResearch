# Opposed quadratic defects at minimal order-six width

Let \(A,\mathbf b\) be any seven-stage order-six strict SDIRK over
an ordered field, with common nonzero diagonal \(\gamma\).
The proof uses the reviewed rooted-tree conditions and applies to
zero or signed output weights, repeated clocks, and exterior clocks.
The forward grade-three rank is either 5 or 6.
In the rank-six branch D(1) is automatic and the two paid quadratic
defect *rows* share a line, even when the diagonal matrix of weights
is singular. In the rank-five branch the forward cubic and the
reverse space have explicit smaller forms. These are structural
claims, not exclusions of either branch.

## Paid spaces and the line argument

Write \(\mathbf c\coloneqq A\mathbf1\),
\(C\coloneqq\operatorname{diag}(\mathbf c)\),
\(\mathbf y\coloneqq\mathbf1-\mathbf c\), and
\(Y\coloneqq I-C\).
For stage grade \(|t|-1\), use the scalar profile
\(f_t(x)\coloneqq |t|x^{|t|-1}/t!\) and actual native column
\(\boldsymbol\Phi_t(A)\). Let \(E_j\) be the span of these
columns through grade \(j\), and \(F_j\) their pure defect span:
the span of \(\boldsymbol\Phi_t(A)-f_t(\mathbf c)\) on the same
range. Let
\(U_j\coloneqq\operatorname{span}(\mathbf1,\mathbf c,\ldots,
\mathbf c^{\odot j})\). These definitions give \(E_j=U_j+F_j\).
Use the paid weighted pairing
\(\langle\mathbf u,\mathbf v\rangle_b\coloneqq
\mathbf b\cdot(\mathbf u\odot\mathbf v)\).
Tree products and unary extensions give the graded rules:
\(A E_j, C E_j\subseteq E_{j+1}\);
\(A F_j, C F_j\subseteq F_{j+1}\);
and \(F_i\perp_b E_j\) when \(i+j\le5\).

Let \(R\coloneqq C A-A C-A^2\) be the checked price-two Volterra
commutator. It maps \(E_j\) into \(F_{j+2}\): the corresponding
scalar expression is \(xJf-J(xf)-J^2f=0\).
It is lower triangular with diagonal \(-\gamma^2\), so it is
invertible. Put
\[
\begin{gathered}
\mathbf q\coloneqq A\mathbf c-\mathbf c^{\odot2}/2,\qquad
\mathbf d\coloneqq\mathbf b^\mathsf T A-\mathbf b^\mathsf T Y,\\
\mathbf q_{\mathrm{row}}\coloneqq
 \mathbf b^\mathsf T\operatorname{diag}(\mathbf q),\qquad
\overline{\mathbf q}_{\mathrm{row}}\coloneqq
 \mathbf b^\mathsf T Y A-\mathbf b^\mathsf T Y^2/2 .
\end{gathered}
\]
The last three symbols are physical covectors. Their definitions
require no division by weights. The paid adjoint primitive identities
give \(\mathbf d\in\operatorname{Ann}E_4\) and
\(\overline{\mathbf q}_{\mathrm{row}}\in\operatorname{Ann}E_3\).
Explicitly, pairing against a grade-\(j\) tree replaces
\(A\boldsymbol\Phi_t\) by \(J f_t\) on the weighted output, and
\(\int_0^1 y^kJf_t=\int_0^1 y^{k+1}f_t/(k+1)\) uses only degrees
\(j+k+1\le5\). Also
\(\mathbf q_{\mathrm{row}}\in\operatorname{Ann}E_3\) by the
pure-product grade bound. The price-two rule gives the nonzero row
\[
\mathbf b^\mathsf T R\in\operatorname{Ann}E_3 .
\]
It is nonzero because \(R\) is invertible and
\(\mathbf b^\mathsf T\mathbf1=1\). Thus \(\dim E_3\le6\).

**Codimension-one reflection lemma.** More generally, for any
nonsingular lower triangular tableau of order \(p\ge3\),
\(\dim E_{p-3}=s-1\) implies \(D(1)\). In fact
\(\operatorname{Ann}E_{p-3}=\operatorname{span}(\mathbf b^\mathsf T R)\).
Let \(\mathbf d=\mathbf b^\mathsf T(A-Y)\) as above. It kills
\(E_{p-2}\), so \(\mathbf d,\mathbf d C,\mathbf d A\) lie in this
same line. If \(\mathbf d\ne0\), the line is invariant under \(C\)
and \(A\), hence \(\mathbf d R\) remains in it. Invertibility of
\(R\) then implies \(\mathbf d\in\operatorname{span}
(\mathbf b^\mathsf T)\). This is impossible since \(\mathbf d\mathbf1=0\)
but \(\mathbf b^\mathsf T\mathbf1=1\). This argument uses no equal
diagonal or nonzero-output hypothesis.

## The two ranks and actual end constraints

The first two physical clocks are distinct. Otherwise \(c_1=c_2=\gamma\)
and \(a_{21}=0\), so the first two stages have identical values
on every tree by their identical self actions. Merging their output
weights and all outgoing coefficients produces an order-six
six-stage common-diagonal tableau, contradicting the established
floor. The first-two-coordinate values
\[
q_1=\gamma^2/2,\qquad
q_2=2\gamma c_2-\gamma^2-c_2^2/2,\qquad
((A-\gamma I)\mathbf q)_1=0,\quad
((A-\gamma I)\mathbf q)_2=(c_2-\gamma)q_1
\]
make \(\mathbf q,(A-\gamma I)\mathbf q\) independent in \(F_3\).
Also \(U_2\) has a nonsingular Hilbert Gram matrix (determinant
\(1/2160\)) and \(F_3\perp_b U_2\), so \(\dim E_3\ge5\).
Likewise \(E_2\) has dimension four, \(R(E_2)\subseteq F_4\),
and \(U_1\cap F_4=0\); hence \(\dim E_4\) is 6 or 7.
The last weight \(b_7\ne0\), since a zero-weight terminal row can
be deleted without changing earlier stage values.

**Rank six.** The codimension-one lemma gives \(\mathbf d=0\).
Consequently \(c_7=1-\gamma\) and
\(b_7 a_{76}=b_6(y_6-\gamma)\). Here \(b_6\ne0\): if it were
zero, \(a_{76}=0\), and row six would have no output weight and no
remaining later dependency. Deleting it would violate the same floor.
The exactly paid row identity
\[
\mathbf b^\mathsf T R
=\mathbf d Y-\mathbf d A-2\overline{\mathbf q}_{\mathrm{row}}
\]
follows by expanding \(C=I-Y\).
Therefore \(\overline{\mathbf q}_{\mathrm{row}}\) spans
\(\operatorname{Ann}E_3\) and
\(\mathbf q_{\mathrm{row}}\) is a multiple of it, possibly zero.
In actual terminal coordinates
\[
(\overline q_{\mathrm{row}})_7=b_7\gamma^2/2,\qquad
(\overline q_{\mathrm{row}})_6=
  b_6(2\gamma y_6-\gamma^2-y_6^2/2).
\]
These match the forward first-two-coordinate formulas without
postulating a global weighted transpose in the singular-weight
case. If \(\mathbf q_{\mathrm{row}}\ne0\), then \(q_7\ne0\)
and the ratio \(q_6/q_7\) is the same quadratic ratio as
\(q_2/q_1\) with \(c_2\) replaced by \(y_6\).

**Rank five.** Now
\(F_3=\operatorname{span}(\mathbf q,(A-\gamma I)\mathbf q)\)
and \(E_3=U_2\oplus F_3\). Thus the shifted cubic Legendre column
\(20\mathbf c^{\odot3}-30\mathbf c^{\odot2}+12\mathbf c-\mathbf1\)
lies in \(F_3\): it pairs to zero with \(U_2\) by paid quadrature.
In the actual first two rows this also gives
\[
(C-\gamma I)\mathbf q
  = (q_2/q_1)(A-\gamma I)\mathbf q,\qquad
[A,R]\mathbf1=0.
\]
For the first identity, both sides are in \(F_3\) and their
first two entries determine them. For the second, the commutator
is between strict lower triangular parts of \(A,R\), since their
diagonals are scalar. Its first two entries on \(\mathbf1\) vanish,
and its column is pure of grade at most three, since \(R\mathbf1=-2\mathbf q\).
If \(D(1)\) fails in this branch, \(\mathbf d\ne0\) and
\(\dim E_4=6\), \(F_4=R(E_2)\). Moreover
\(\mathbf d,\mathbf d C,\mathbf d A\) span the two-dimensional
annihilator of \(E_3\): the one-dimensional possibility would again
invert \(R\) to put \(\mathbf d\) in the output line, as above.
No exclusion of this two-dimensional branch is needed for the
rational construction.

## A support consequence without dividing by zero weights

Restrict the weighted form to the set of rows of individually
nonzero weight, of size \(m\). The restriction is nondegenerate;
\(U_2\) still has the same Hilbert Gram matrix and its orthogonal
complement has dimension \(m-3\).
Both \(\mathbf q\) and \(C\mathbf q\) on these coordinates belong
to that complement and are orthogonal to \(\mathbf q\), by the
paid \(q^2\) and \(c q^2\) moments. If \(m\le4\), an
isotropic \(\mathbf q\) is necessarily zero there. If \(m=5\)
and the restricted \(\mathbf q\ne0\), its perpendicular in the
two-dimensional complement is its own line. Consequently
\(C\mathbf q\) is proportional to \(\mathbf q\) on these active
coordinates, confining its support to a single clock.
If at least four distinct sites have nonzero aggregate mass, each
site on the five active rows has at most two rows and nonzero
aggregate mass. A nonzero isotropic vector at a single site
cannot have zero weighted sum over one or two such rows. (For
two rows, substitute \(q_j=-b_iq_i/b_j\) into the square as in the
order-five argument.) Thus \(\mathbf q\) again vanishes on all
active coordinates.

Over \(\mathbb Q\), the four-site quadrature premise holds at
order six by the already proved degree-four obstruction. Also
\(q_2\ne0\), because its vanishing would give
\(c_2=(2\pm\sqrt2)\gamma\). Hence any rational order-six
tableau with at most five nonzero output weights has its first two
weights zero and is quadratic-stage exact wherever the output
weight is nonzero. The
[seven-stage rational splice](order-six-seven-stage-rational-splice.md)
has exactly this structure.

## The additional cubic pairings when the weight matrix is invertible

In the rank-six branch, if all seven weights are nonzero, the raw
line gives the normalized \(A^\star=W^{-1}A^\mathsf TW\) with
\(W=\operatorname{diag}(\mathbf b)\),
\(A^\star\mathbf1=\mathbf y\), and
\(A^\star\mathbf y-\mathbf y^{\odot2}/2=\lambda\mathbf q\)
for some nonzero \(\lambda\). In this chart the remaining exact
order-six gate is \(B(6)\), together with
\[
\begin{gathered}
\mathbf q\perp_b U_3,\qquad
\langle\mathbf q,\mathbf q\rangle_b
=\langle\mathbf q,C\mathbf q\rangle_b=0,\\
\mathbf r,\mathbf s\perp_b U_2+\operatorname{span}(\mathbf q),
\qquad
\mathbf r\coloneqq A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3,\quad
\mathbf s\coloneqq A\mathbf q .
\end{gathered} \tag{*}
\]
The tests are necessary by tree products and their grades.
For sufficiency, the shared line gives
\(A^\star\mathbf c=(\mathbf1-\mathbf c^{\odot2})/2-\lambda\mathbf q\).
The grade-three errors span \(\mathbf q,C\mathbf q,\mathbf r,\mathbf s\)
and are orthogonal to \(U_2\) by (*).
Grade-four errors add
\[
A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4,\quad
A(C\mathbf q),A\mathbf r,A\mathbf s,\quad
C^2\mathbf q,C\mathbf r,C\mathbf s,\mathbf q^{\odot2}.
\]
They are orthogonal to \(U_1\): use (*), the two displayed adjoint
actions on \(\mathbf1,\mathbf c\), and the degree-five quadrature.
At grade five, a unary primitive can add \(A F_4\) and
\(A\mathbf c^{\odot4}-\mathbf c^{\odot5}/5\), killed in the output
by \(D(1)\). A single bad primitive at a multi-branch root is
paired with its remaining clock power, paid by the lower
orthogonalities. Two bad primitive factors cost at least four:
the only products needed are \(C\mathbf q^{\odot2}\) and
\(\mathbf q\) times grade-three defects, all paid by (*).
Three bad factors cost at least six, beyond grade five.
This proves the full tree order without introducing independent
higher reverse coordinates.

In this full-support shared-line chart the chronologically reflected
\(A^\star\) also has order six. For its cubic defects
\(A^\star\mathbf y^{\odot2}-\mathbf y^{\odot3}/3\) and
\(A^\star(\lambda\mathbf q)\), the tests in (*) transfer directly
by adjointness: pair against \(U_2\) using \(A\) on
\(\mathbf1,\mathbf c,\mathbf c^{\odot2}\), and against \(\mathbf q\)
using \(\mathbf s\) and \(\langle\mathbf q,\mathbf s\rangle_b=0\).
The other tests are invariant under replacing \(x\) by \(1-x\)
and scaling \(\mathbf q\) by \(\lambda\). The sufficiency just
proved then applies. Consequently the final two clocks are distinct
in this full-support shared-line branch by the same two-row merge
argument at the opposite end. No such normalized reflection is
assumed when a weight vanishes.
