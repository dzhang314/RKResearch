# Exact rational order ten in thirteen diagonally implicit stages

The [literal tableau](tableau.json) has **exact order ten in 13 stages over the rationals**. Combined with the [rational lower bound of 12](../causal-profile-reduction/dirk-order10-rational-lower-twelve.md), this leaves the rational minimum in **12–13**. It is ordinary DIRK, with unequal nonzero diagonal entries (for example \(1/14\) and \(13/108\)), not an explicit or common-diagonal tableau. All thirteen retained rows are distinct.

It also specializes to exact order ten over any **nonzero commutative ring** where \(D=126767366286331069785024000\) is invertible. All tableau and weight denominators divide \(D\). The raw eleventh-bush defect is \(1/27371520\); the factorial-scaled defect is \(1/2488320\), a unit in the localization because \(2488320\mid D^2\). This is not an upper bound over every ring inverting \(10!\). The known real-algebraic 11-stage endpoint is unchanged.

## Seven opening rows and two literal sharing ports

Take opening clocks
\[
  (0,1/7,1/9,2/9,123/220,q,r),\qquad q=3/4,\quad r=1/4.
\]
Let \(Jf(X)=\int_0^X f(z)\,dz\). Each nonzero opening row is the anchored interpolatory quadrature using the listed physical slot numbers, including its own slot:
\[
  2:(1,2),\quad3:(1,2,3),\quad4:(1,3,4),\quad
  5:(1,3,4,5),\quad6:(1,4,5,6),\quad7:(1,4,5,6,7).
\]
All rows pay \(A\mathbf1=\mathbf c\) and \(A\mathbf c=\mathbf c^2/2\). The second row is trapezoidal, the third pays quadratics, and the fourth is Simpson (so also pays cubics) and avoids the second row. Rows \(1,4,5,6,7\) therefore return truthful polynomial values on **every actual tree** through size five. The decoder \(\Pi\) interpolates their actual coordinates onto \(P_4\).

At \(q\), writing \(u=2/9,p=123/220\), the four-node hull satisfies
\[
  \int_0^q X(X-u)(X-p)(X-q)\,dX=0
  \quad\text{because}\quad p=\frac{q(3q-5u)}{5(q-2u)} .
\]
Thus slot 6 pays degree four with four available clean nodes. Slot 7 gets that degree by ordinary five-node interpolation. Both \(q,r\) return true derivative data through size six. Let \(\rho_t=f_t-\Pi\boldsymbol{\Phi}_t(A_{\rm old})\), with \(f_t(X)=|t|X^{|t|-1}/t!\). The literal prefix replay finds the size-six residual space
\[
  F_5=X(X-q)(X-r)P_2 ;
\]
it vanishes at the three displayed nodes, and its exact rank is three. Residuals for size-seven trees have degree at most six and vanish at zero.

## Eight reflected rows, then two paid reductions

Use the symmetric nine-node degree-nine quadrature with centered proper coordinates \(0,\pm 1/3,\pm 5/6,\pm 1/2\) and endpoints \(\pm1\). Its origin mass is assigned to the original zero row. The eight nonzero physical clocks in **reverse chronology** are
\[
  \mathbf x=(1,2/3,1/3,11/12,1/2,1/12,r,q),\qquad
  \mathbf y=\mathbf1-\mathbf x .
\]
Let \(\mathbf w\) be their quadrature weights and \(L\) the lower triangular normalized weighted transpose of the suffix block. Choose its actions
\[
 L\mathbf1=\mathbf y,\qquad
 L\mathbf y=\mathbf y^2/2,\qquad
 L\mathbf y^2=\mathbf y^3/3+\mathbf g .
\]
For the seven proper clocks set \(g_i=\tau/(w_i x_i P_7'(x_i))\), with \(P_7\) their nodal polynomial; at physical one set \(g_1=0\). The constant \(\tau\) pays the forced trapezoidal value at the second reflected row. Then \(\langle\mathbf g,\mathbf x^j\rangle_{\mathbf w}=0\) for \(1\le j\le6\) by Lagrange interpolation. In particular it kills all size-six and size-seven source residuals and the primitives of the size-six ones.

The [primal/dual word proof](../../lower-bounds/proof-dependencies/rk_first_overlap_primal_dual_gluing_20261123.md) now needs only two new tests on \(F_5\):
\[
   \big\langle L\mathbf y^3-\mathbf y^4/4,E F_5\big\rangle_{\mathbf w}=0,
   \qquad
   \big\langle L\mathbf g,E F_5\big\rangle_{\mathbf w}=0.
\]
Indeed all reverse words through length two are correct before their last primitive; length three can see only the cubic \(\mathbf g\), and its pairing against a source primitive is already zero. By degree nine two first source errors cannot interact. The construction pays the two tests together with a five-variable exact linear solve: one available change on reflected row 4 and two each on rows 5 and 6. Its matrix and augmented matrix both have rank five.

To find an exact grid rather than approximate the missing scalar: let \(F=X(X-q)(X-r)(X-1/2)(X-1/12)\), the unique line in \(F_5\) not seen by the two latest free response rows. On the first four reflected rows, \(\mathbf g\) is the evaluation of a cubic \(G\). Their last-direction responses are dependent by that cubic. On \(F\), after the cubic moment of \(\mathbf g\) has been paid, the compatibility is thus \(\int_0^1 F J^*G=0\), where \(J^*f(X)=\int_X^1 f(z)\,dz\). In centered variables with early proper sites \(a,-a,b\) and late sites \(0,-b,c,-c\), the [exact selection calculation](check_selection_gate.py) factors that condition, up to normalization, as
\[
     (7c^2-3)(6bc^2-3b-3c^2+2)=0 .
\]
The rational family \(b=(3c^2-2)/(6c^2-3)\) supplies the selected \(c=1/2,b=5/6,a=1/3\). The factor is a way to find the fixture, not an assumption in the order checker.

In forward coordinates the suffix has block \(T\) and prefix cross block \((EJ-TE)\Pi\). Both first suffix rows, in chronology \(q,r\), are exactly the corresponding old **whole** rows, including their zero padding. This is verified entry-by-entry before contraction. Redirect all columns and both weights to the respective old rows. The literal count is \(7+8-2=13\), not a compression of scalar weights alone. The identities prove all tree values are preserved by the two reductions.

## Independent replay

The constructor needs SymPy. The literal arithmetic checker needs only the Python standard library and checks all **1,205** unordered rooted shapes through ten, plus the next-bush failure, without any reference to the projection proof or constructor. Commutativity makes a tree's sibling presentation irrelevant.

    python3 -B audit_tableau.py
    python3 -B check_selection_gate.py
    python3 -B build13.py --emit /tmp/dirk-thirteen-rebuilt.json
    cmp tableau.json /tmp/dirk-thirteen-rebuilt.json
    sha256sum -c arithmetic-sha256.txt

The [end-to-end Lean upper certificate](../dirk10-thirteen-native-upper/README.md) checks exact order, triangularity, and specialization over any nonzero commutative ring inverting the displayed denominator on Lean/Mathlib 4.36.0.
