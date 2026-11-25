# A six-stage rational strict SDIRK method of exact order five

This was the first improvement from eight to six rational stages.
The [later five-stage construction](order-five-five-stage-repeated-clock.md)
now attains the rational minimum. The construction reuses its two-row
zero-output core and its four-site quadrature; each site now needs only
one suffix stage. Both reverse repairs use the same two predecessor
clocks. There is no search over tableau coefficients.

## Literal tableau

The common diagonal is one. All entries above the displayed lower
triangle are zero.

| Row | Entries |
|---:|---|
| 1 | \(1\) |
| 2 | \(-1,1\) |
| 3 | \(-1/2,1/2,1\) |
| 4 | \(-4/9,1/9,0,1\) |
| 5 | \(1187/250,-29/250,-98/25,-189/125,1\) |
| 6 | \(-36,-3/2,65/2,81/14,-25/14,1\) |

The weights and row sums are
\[
\mathbf b\coloneqq(0,0,5/48,27/56,125/336,1/24),\qquad
\mathbf c\coloneqq(1,0,1,2/3,1/5,0).
\]
The exact checker derives these rows in the construction below and then,
independently of that derivation, evaluates the literal tableau on all
rooted trees through order six. All 17 trees of orders one through five
satisfy \(t!\,\mathbf b\cdot\boldsymbol{\Phi}_t(A)=1\). All 20 order-six
trees fail. In particular, the order-six tall tree has weight \(-5/24\),
not \(1/720\). The statement is about the reviewed rooted-tree order;
no stability property is claimed.

## The reusable two-donor criterion

Work over a characteristic-zero field. Let the common nonzero diagonal
be \(\gamma\); pick a second core clock \(\eta\ne\gamma\). Take
\[
G\coloneqq
\begin{pmatrix}\gamma&0\\ \eta-\gamma&\gamma\end{pmatrix},
\qquad
\Pi\mathbf v\coloneqq
v_1\frac{x-\eta}{\gamma-\eta}
+v_2\frac{\gamma-x}{\gamma-\eta}.
\]
Here \(\Pi\) interpolates a core vector at \(x=\gamma,\eta\). The core
weights are both zero. Suppose the suffix has an exact degree-four
quadrature with nonzero weights \(w_i\). Write \(x_i\) in **reverse stage
order**, put \(y_i\coloneqq1-x_i\), and require \(y_1=\gamma\) with
\(y_2\ne y_1\). This aligns the first reflected stage with the specified
diagonal; it need not align the first primal suffix stage with it.

Let \(L\) be lower triangular in this reflected order, all diagonal
entries \(\gamma\), with \(L\mathbf 1=\mathbf y\). Define
\[
\boldsymbol\delta\coloneqq L\mathbf y-\mathbf y^{\odot2}/2,\qquad
N(x)\coloneqq(x-\gamma)(x-\eta),\qquad
M(x)\coloneqq x^2/2-2\gamma x+\gamma^2.
\]
Use the reflected weighted transpose \(W^{-1}L^\mathsf{T}W\), with
\(W\coloneqq\operatorname{diag}(\mathbf w)\), for the primal suffix
block in reverse coordinates. Reverse both indices to obtain the
chronological lower triangular block \(T\). In that chronological order
let \(E\) be evaluation at the suffix clocks, and \(J\) the polynomial
primitive from zero. The full coupling and tableau are
\[
K\coloneqq(EJ-TE)\Pi,\qquad A\coloneqq
\begin{pmatrix}G&0\\K&T\end{pmatrix}.
\]
The suffix weights are also reversed back into chronological order.
Since \(\Pi\mathbf 1=1\), this matrix has the specified physical row
sums.

**Criterion.** Given these hypotheses the tableau has order at least
five if and only if
\[
\sum_i w_i\delta_i N(x_i)=0,\qquad
\sum_i w_i\delta_i M(x_i)=0.
\]
The first two \(\delta_i\) are forced by the diagonal and row sums:
\[
\delta_1=\gamma^2/2,\qquad
\delta_2=2\gamma y_2-\gamma^2-y_2^2/2.
\]
Every later \(\delta_i\) can be assigned independently using only the
first two reflected columns: their distinct clocks make the map
\((a,b)\mapsto(a+b,y_1a+y_2b)\) invertible. Thus any two later
representatives whose weighted \((N,M)\) sample vectors are independent
can pay both residuals using the **same** two donor stages. In a
four-site suffix this is just one \(2\times2\) solve.

### Proof of the criterion

For a rooted tree \(t\) of grade \(|t|-1\), let
\(f_t(x)\coloneqq |t| x^{|t|-1}/t!\). Unary extension is \(f_{[t]}=Jf_t\);
adding a child multiplies by its scalar primitive. The reviewed
\(\boldsymbol{\Phi}_t\) has the same recursion with coordinatewise product
and the matrix \(A\) in place of \(J\). Let
\(\boldsymbol u_t\coloneqq\boldsymbol{\Phi}_t(G)\), and let
\(\boldsymbol e_t\) be the suffix vector minus \(Ef_t\). An actual unary
step satisfies
\[
\boldsymbol e_{[t]}=T\boldsymbol e_t+(TE-EJ)\rho_t,\qquad
\rho_t\coloneqq f_t-\Pi\boldsymbol u_t.
\]
The core interpolates grades zero and one exactly. At grade two the
bush residual is \(N\); the chain gives \(M\) because
\(\Pi(G\mathbf c_{\mathrm{core}})=2\gamma x-\gamma^2\). Accordingly
suffix errors start at grade three. Through grade four, any tree
contains at most one nonzero error factor at a given root, because two
such factors would cost at least six grades. The only possible output
tests are:
* a bare source \((TE-EJ)\rho_t\) for \(\deg\rho_t\le3\);
* the same source from grade two, followed by \(T\) or multiplication
  by \(x\).

The exact degree-four quadrature equates these polynomial pairings
with \(\mu\), the formal uniform integral on \([0,1]\).
For \(J^*g(x)\coloneqq\int_x^1 g(t)\,dt\), the identity
\(\mu((J^*g)f)=\mu(gJf)\) holds on monomials \(f=x^r,g=x^t\):
both sides equal \(1/((r+1)(r+t+2))\). Only degrees through four
are used. Since \(L\) is the weighted adjoint of \(T\) and
\(L\mathbf 1=\mathbf y\), the bare source has zero output pairing for
every such polynomial. The \(T\) successor gives the pairing with
\(L\mathbf y-\mathbf y^{\odot2}/2\). The clock successor gives its
negative since \(L\mathbf x=\mathbf y-L\mathbf y\) and
\(J^*x=y-y^2/2\). Hence precisely the two stated pairings suffice.
They are also necessary: take the tree obtained by extending either
grade-two tree twice. Its last new source has the already-vanishing
bare pairing; its propagated first source is just the corresponding
\(\boldsymbol\delta\) pairing. Finally, zero weighted error and the exact
quadrature identity \(\mu(f_t)=1/t!\) give the reviewed all-tree order.

## The exact shared-donor solve

Take \(\gamma=1\), \(\eta=0\), and the reflected order
\[
\mathbf x\coloneqq(0,1/5,2/3,1),\quad
\mathbf y\coloneqq(1,4/5,1/3,0),\quad
\mathbf w\coloneqq(1/24,125/336,27/56,5/48).
\]
At the third row \(N(2/3)=-2/9\); at the fourth \(N(1)=0\) but
\(M(1)=-1/2\). This is an invertible triangular pairing matrix.
The forced errors are \(1/2,7/25\); the two equations give
\(\delta_3=-7/45\), \(\delta_4=9/5\). Recovering both rows with the
same first two donors gives
\[
L\coloneqq\begin{pmatrix}
1&0&0&0\\
-1/5&1&0&0\\
1/2&-7/6&1&0\\
13&-14&0&1
\end{pmatrix}.
\]
The formulas for \(T\) and \(K\) now give the literal six rows above.
The older six suffix stages used duplicate endpoints; no such
duplicate is needed to make these two repairs independent.

## Five stages remain open

The two core rows cannot be literally identified with their equal-clock
suffix stages: their order-three chain values differ. The separate
[five-stage condition](order-five-five-stage-necessary.md) gives a stronger
necessary signature and square condition, without excluding five.

## Replay and provenance

Run `python3 check-six-stage-splice.py` from this directory. It uses
Python's standard library and exact rational arithmetic only.
`six-stage-splice-numerators.json` encodes the same tableau for the
reviewed finite scaled-tree checker. No Lean compiler was run here.

The construction starts from the published [eight-stage certificate and
four-site rational quadrature](order-five.md), and uses the reviewed
`RKResearch.OrderConditions` recursion. No held material is used.

## Lean replay

The exact six-stage existence theorem is in the native module
RKCert.ReviewedNative.RationalStrictSDIRKSixStageFiveUpper. It uses the
reviewed HasOrder predicate and checks the sixth tall-tree failure. The
module compiled and passed an independent kernel replay on Lean 4.36.0.
The typed audit reports only standard axioms.
