# Exact order five over commutative rings: the minimum is six

Let \(R\) be a nonzero commutative ring with identity. The coefficient
equations for order five are the usual rooted-tree equations with
the tree factorial moved to the left. The exact-order-five minimum
for explicit Runge–Kutta tableaux is six if \(120\) is a unit in
\(R\). If \(120\) is not a unit, no tableau satisfies the equations
through order five, regardless of stage count.

Necessity of the unit follows from the five-vertex chain: its scalar
weight times \(120\) must be \(1\). The
[ring-level stage lower bound](../../lean/AuditReviewedNativeERKUniform.lean)
excludes at most five explicit stages. For sufficiency, use these
strict rows of \(A\), with all omitted entries zero, and the weights
\(\mathbf b\):
\[
\begin{array}{c|rrrrr}
1\\
2&1/2\\
3&1/4&1/4\\
4&2/9&0&1/9\\
5&-5/18&-5/36&0&5/4\\
6&27/5&2&-1&-9&18/5
\end{array}
\qquad
\mathbf b=(8/75,\ 0,\ 1/15,\ 9/20,\ 9/25,\ 1/60).
\]
The row sums are \((0,1/2,1/2,1/3,5/6,1)\).
This tableau is a specialization of
[Hairer, Nørsett and Wanner, §II.5, Algorithm 5.2](https://moodle.utc.fr/file.php/336/Hairer_Noersett_Wanner._Solving_ordinary_differential_equations_vol.1._Nonstiff_problems_2ed._revised_Springer_2008_ISBN_3540566708_593s_MNd_.pdf),
using \(c_2=c_3=1/2,\ c_4=1/3,\ c_5=5/6,\ a_{42}=0\). No priority for
this specialization is claimed.

The [exact replay](check_order_five.py) enumerates the \(1,1,2,4,9\)
rooted trees of orders one through five and verifies all 17 equations
using fractions. The tree evaluation starts at
\(\boldsymbol{\Phi}_\bullet(A)=\mathbf 1\). Unary extension applies
\(A\), and rooted sum multiplies the two columns coordinatewise.
Every displayed coefficient belongs to \(\mathbb Z[1/30]\). Thus
the equalities checked in \(\mathbb Q\) hold in that subring and map
to \(R\) whenever \(120\) is a unit.

The sixth-order equations fail in every such nonzero \(R\), not just
over \(\mathbb Q\). At the six-vertex chain there is exactly one
strict path of length five. Its weight is
\[
b_6 a_{65}a_{54}a_{43}a_{32}a_{21}=1/960.
\]
The cleared defect is \(6!/960-1=-1/4\), a unit that stays nonzero
under every allowed base change. In particular, this same tableau has
exact order five over \(\mathbb Z/77\mathbb Z\).
