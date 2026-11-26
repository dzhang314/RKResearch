# Chronological reverse flags with one surplus

Let \(K\) be a field over which the factorials of the order under discussion are units. Write \(Y\) for the diagonal reflected-clock operator on actual reverse coordinates, \(N\) for the lower triangular reverse transpose, and \(M_j\) for the actual zero-density one-mark space of grade at most \(j\). The arguments below also apply to terminal-zero spaces when the one-mark operations and primitive errors preserve that zero. We use only nesting, the actual inclusions \(YM_j,NM_j\subseteq M_{j+1}\), and paid Hermite exits. Products, when used in the companion note, have a single marked factor.

Write \(\mathcal P_d\) for polynomials of degree at most \(d\), with \(\mathcal P_d=0\) for \(d<0\). One surplus over unit growth means there is exactly one double step and every other increase is one, or that an actual subflag such as the \(D_3\)-word flag has codimension one in an otherwise unit band. These are different viewpoints and both are covered.

## 1. The double step is a hyperplane in a one-degree trim

Suppose the unique double step lands at \(t\) and is followed by at least one unit step. Assume the relevant spaces are not \(Y\)-invariant. This is guaranteed, for example, when the band starts at grade at least six and the terminal grade is at least seven: paid outgoing and incoming Hermite gains for an invariant space are respectively \(\lfloor j/2\rfloor\) and \(\lfloor(j-1)/2\rfloor\), while no rank gain in this band exceeds two. For a terminal-zero flag the scalar primitive errors used for these tests must also be terminal-zero.

The late band then has a fixed invariant direct summand \(U\) and a single head \(\mathbf w\):
\[
 M_j=U\oplus\mathbf w\mathcal P_{R+j-t-1}(Y)
                                  \qquad(t\le j\le H).
\tag{1}
\]
This is the elementary codimension-one clock escape. The subspaces of \(M_t\) whose first \(i\) clock multiples stay in \(M_t\) drop by at most one per step, by injectivity of clock multiplication into the preceding quotient, and stabilize at \(U\). Choosing a vector before the last drop gives the claimed head. Noninvariance of each subsequent space forces its next clock multiple to fill the one available dimension. Use a complement to \(U\) in each actual clock fibre. Noninvariance at the final grade gives at least \(R+H-t+1\) distinct effective head labels, so consecutive polynomial comparisons do not wrap around an interpolating hull.

Since \(YM_{t-1}\subseteq M_t\), the polynomial of any vector from \(M_{t-1}\) has degree at most \(R-2\): a nonzero top coefficient at degree \(R-1\) would give a forbidden next power. Thus
\[
 M_{t-1}=\ker\chi\ 	ext{ inside }\ U\oplus\mathbf w\mathcal P_{R-2}(Y)
\tag{2}
\]
for a nonzero row \(\chi\). The trimmed space has dimension \(\dim M_t-1\) and the old space has dimension \(\dim M_t-2\). Require \(R\ge2\) for this classification. If \(R=1\), the trim is \(U\), with \(M_{t-1}\) only a hyperplane inside it. Outgoing Hermite with at least three detectors at grade \(t\) excludes this case when the following gain is one, since then \(\dim M_{t+1}\ge\dim U+3=\dim M_t+2\). Noninvariance alone does not exclude it. Put \(V_0\coloneqq U\oplus\mathbf w\mathcal P_{R-3}(Y)\). A complete test is:

* If \(\chi|_{V_0}=0\), the row is the leading coefficient. The old space is \(V_0\) and its clock prolongation has codimension one in \(M_t\).
* Otherwise the old space has a vector with nonzero coefficient at degree \(R-2\). Its clock multiple provides the top degree at \(M_t\). There is a second clock direction precisely when \(\chi\circ Y\) is not proportional to \(\chi\) on \(V_0\). Indeed a vector in \(\ker\chi\cap V_0\) witnessing that failure gives a new direction within the trim, independent of the top-degree one.
* In the proportional case a scalar \(a\in K\) satisfies \(\chi(Yz)=a\chi(z)\) on \(V_0\). Writing \(z=\mathbf u+\mathbf wP(Y)\), the row is
\[
                      \chi(z)=\ell(\mathbf u)+cP(a),
\]
where \(\ell(Y\mathbf u)=a\ell(\mathbf u)\) on \(U\). The scalar polynomial coefficients follow by the recursion between consecutive monomials. The invariant part \(\ell\), if nonzero, lives on the actual clock \(a\); a pure polynomial evaluation may use a clock not physically present.

Thus there are two clock directions consuming the whole double gain, a single clock direction and a spare finite character, or a single clock direction and a spare leading coefficient. No information about a terminal double step without a following rank measurement is inferred from this classification.

If there is at least one preceding unit step, the old space already has one head plus its own maximal clock-invariant part \(U_-\). Its clock extension into grade \(t\) adds exactly one dimension, so the two-clock branch is then unavailable. Denote the old head by \(\mathbf g\). Write
\[
 \delta\coloneqq\dim U-\dim U_-,\qquad
 \mathbf g=\mathbf wL(Y)+\mathbf e .
\]
The old head prolongation into grade \(t\), of rank \(\dim M_t-1\), must be assumed not contained in \(U\), unless this has been certified, for example by the same outgoing Hermite bound with three detectors at \(t\). Hence \(L\ne0\). Comparing all consecutive old head powers paid through \(t\) gives \(\deg L\le1-\delta\). In particular \(\delta\in\{0,1\}\). With \(\delta=0\), subtract an old invariant component to take \(\mathbf e=0\). With \(\delta=1\), \(L\) is constant and \(\mathbf e\) can be supported at the single added core clock \(a\), by subtracting its components in \(U_-\). These statements use actual coordinate fibres rather than orthogonal complements.

## 2. The same line classification without observing a double step

Suppose \(M_j\) is already a unit band of the form (1), and \(B_j\) is any actual codimension-one subflag with \(B_j+YB_j\subseteq B_{j+1}\). Write \(\phi_j\) for a nonzero annihilator of \(B_j\) inside \(M_j\).

If \(\phi_{j+1}|_{M_j}\ne0\), normalize this restriction to \(\phi_j\). Then \(\phi_{j+1}Y=a_j\phi_j\) on \(M_j\). On \(U\) this is the eigen-covector condition; on the head monomials it is a geometric recursion. Thus both rows have the finite form above, and comparing at the next common grade forces the same \(a_j\) throughout consecutive finite transitions. In particular,
\[
                  (Y-a_j I)M_j\subseteq B_{j+1}.
\tag{3}
\]

If the restriction is zero, \(\phi_{j+1}\) is the new highest coefficient, and \(\phi_{j+1}Y\) is the prior highest coefficient. This is the leading-coefficient case; it gives directly
\[
                              M_j\subseteq B_{j+1}.
\tag{4}
\]
Once an old head has degree at least one, this type cannot change to finite. Indeed a finite restriction at the next grade would send the penultimate power on the old head to a vector where the next functional is nonzero, although the old highest-coefficient functional is zero on that penultimate power. A constant-only initial head does not distinguish finite evaluation from a highest coefficient until a transition is measured.

In the setting of (2), prolong the old space by its clock powers. In the finite case its extension has the same evaluation equation at each later grade, and in the leading-coefficient case it has exactly one less top degree. Thus (3) or (4) is a one-grade operation on the actual leftover direction throughout the late band. If an \(N\)-word enters that direction, the old word flag absorbs it. Once the word flag equals the full space on a noninvariant unit band, equality persists by the clock extension alone.

This classification does not force a finite parameter to be a literal stage clock unless it acts nontrivially on the invariant core. It does not assert that an arbitrary formal word flag is an achieved RK flag.
