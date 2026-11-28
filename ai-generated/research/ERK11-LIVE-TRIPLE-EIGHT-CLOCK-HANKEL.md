# Finite clock atlas for the nonzero-mass ERK11 triple

**Scope.** Continue the [six-group triple reduction](ERK11-SIX-GROUP-TRIPLE-CROSS-PAIR.md): the maximal all-live 17-stage half-clock ERK11 chart with exactly two quadratic carriers, both seventh-stage boundaries new, six active noncarrier clock labels, thirteen active stages (five pairs, one triple), and zero first-response pools on all six labels. This packet concerns **nonzero ordinary scalar mass at the triple**. It gives a **finite algebraic set of possible clock layouts over characteristic-zero fields**, not a contradiction or a count of viable tableaux. The endpoint collision, cofactor pivots, derivative contact, and finite reduction are characteristic zero; the final support restriction uses an ordering. No reverse order eleven is used.

The [standalone exact replay](erk11-live-triple-eight-clock-hankel/replay_specialization.py) verifies the finite-field unit witnesses independently from the fixed polynomial formulas. The tableau, grade, localization, and finite projection arguments are mathematical; no native Lean endpoint is claimed here.

## 1. Endpoint collisions are excluded before making an eight-clock Hankel

Use the left and right physical plateau widths \(a,b\ne0\). The ordinary calibration clocks are \(a,h=a/2\) and \(d=1-b,e=1-b/2\). Each front has four distinct active clock labels: its plateau twice, its half-plateau, and the two other active clocks at its sixth and seventh rows. Both repeated plateau rows are active by the thirteen-active census. Widths, actual response scales, and literal pivots are those of the [two-front reduction](ERK11-SOLE-LATE-CARRIER-TWO-FRONT.md). In particular no zero-response premise is imposed at physical 13.

The scalar moments through degree ten are supplied by the six active labels and the two physical endpoint slots \(0,1\); the two carrier weights cancel at their common clock. All five ordinary pair pools are nonzero by the local pair calculation, and the triple pool is nonzero by hypothesis. A potential scalar endpoint label could still coincide with one active clock; we do not yet divide by this label's pooled mass.

If both endpoints are active, only four nonendpoint active labels remain. Their monic quartic hull times \(X(X-1)\), tested with every polynomial of degree at most four, would make the quartic orthogonal against the nonsingular rational weight-\(X(1-X)\) Gram through degree four. This is impossible without any sign assumption.

If exactly one endpoint is active, the nonendpoint active hull instead has degree five and is proportional to \(R_5+\lambda R_4\), by orthogonality through degree three. Here
\[
 R_4=42X^4-84X^3+56X^2-14X+1,\qquad
 R_5=132X^5-330X^4+300X^3-120X^2+20X-1 .
\]
This only uses an annihilating polynomial on the *possible* support; it does not require a nonzero pooled weight at a colliding endpoint. If all four calibrations avoid the endpoints, the [two-front doubling obstruction](ERK11-TWO-CARRIER-JACOBI-POOL-EXIT.md) gives \(V(\lambda)=V(-\lambda)=0\), impossible by its checked characteristic-zero coprimality. This applies also when calibrations on opposite fronts coincide.

For an active endpoint 1 only a left calibration can be affected: the right \(d,e\ne1\) since \(b\ne0\). If \(a=1\), the interior half-plateau \(1/2\) forces \(\lambda=0\) by \(R_5(1/2)=0,\ R_4(1/2)=1/8\); but \(V(0)\ne0\). If \(a/2=1\), the interior left plateau is 2 and \(\lambda=-903/197\). The right doubling requires \(V(-\lambda)=0\), excluded by \(197^8V(903/197)\equiv4\pmod{13}\) in the [zero-mass clock packet](ERK11-SIX-GROUP-TRIPLE-CROSS-PAIR.md). Reflect the argument for active endpoint 0. Thus the six active labels and the two endpoints are **eight distinct scalar sites, all with live pooled masses**. This is separate from the determinant below.

## 2. Hankel hulls with no generic-pivot exception

Write \(H_6\) for the monic hull of the six active labels and \(w=X(1-X)\). The vanishing hull \(X(X-1)H_6\) on all eight sites and exactness through degree ten give
\[
 \int_0^1 w H_6 X^j=0,\qquad 0\le j\le2 .
\]
All integrals denote the rational polynomial functional, transferred to the field of the tableau.

**Four distinct calibrations.** Put \(P_4=(X-a)(X-h)(X-d)(X-e)\) and \(H_6=P_4(X)(X^2+uX+v)\). For \(m_j=\int wP_4X^j\), indexed \(0\le j\le4\), the three equations are \(m_{j+2}+u m_{j+1}+v m_j=0\). Hence
\[
 D(a,b)=\det\begin{pmatrix}
  m_0&m_1&m_2\\m_1&m_2&m_3\\m_2&m_3&m_4
 \end{pmatrix}=0.
\]
The pivot is \(\Delta=m_0m_2-m_1^2\ne0\) on **every actual layout**. If \(\Delta=0\) and \(m_0=0\), then \(m_1=0\) and the actual recurrence forces \(m_2,m_3,m_4=0\), impossible by the nonsingular weighted quartic Gram. If \(\Delta=0\) and \(m_0\ne0\), let \(t=m_1/m_0\). The equality \(m_2=m_0t^2\) and first recurrence give \(t^2+ut+v=0\); the remaining recurrences give \(m_j=m_0t^j\) through degree four. Thus \(P_4(X)(X-t)\) is a monic quintic orthogonal through degree three and contains both calibration doublings, again contradicting the quintic \(V(\lambda),V(-\lambda)\) obstruction. This permits \(t\) equal to an existing label, since doubling does not require simplicity. Cramer's rule fixes
\[
 u=(m_1m_2-m_0m_3)/\Delta,\qquad
 v=(m_1m_3-m_2^2)/\Delta.
\]

**Three distinct calibrations.** The two active plateau rows on each front ensure \(a\ne d\), since four occurrences at one active clock are impossible. Each width is nonzero, so its half differs from its plateau. The only overlaps are
\[
 h=e:\ b=2-a;\qquad a=e:\ b=2-2a;\qquad h=d:\ b=(2-a)/2 .
\]
The half-half overlap cannot accompany a mixed overlap without collapsing a plateau with its own half. The two mixed overlaps cannot both occur, because each forces a triple at its plateau and those clocks differ. Thus there are no one- or two-distinct-calibration cases.

Let \(P_3\) be the monic hull of the three calibrations, and write \(H_6=P_3(X)(X^3+uX^2+vX+s)\). With \(m_j=\int wP_3X^j\) the matrix \(M=(m_{i+j})_{0\le i,j\le2}\) sends \((s,v,u)^T\) to \(-(m_3,m_4,m_5)^T\). It is invertible on the actual chart. If not, a nonzero polynomial \(S\) of degree at most two from its null space makes \(P_3S\) orthogonal through degree two. Symmetry and consistency of the actual monic cubic system make it orthogonal also to \(X^3\). If its degree is three, the weighted cubic Gram is nonsingular, a contradiction. If degree five, apply the two-front quintic doubling. If degree four, it is a nonzero multiple of \(R_4\), impossible already for its two left roots \(a,a/2\). The identity is
\[
 (-1428X^3+4452X^2-3542X+235)R_4(X)
 +(2856X^3-3192X^2+700X-22)\,8R_4(X/2)=59 .
\]
Thus each overlap has \(b\) uniquely linear in \(a\) and a unique cubic cofactor by a proved-live pivot, even at exceptional values of later elimination polynomials.

## 3. Literal derivative contact of rows 7 and 11

This clock-only gate holds in the underlying **both-new** two-front chart irrespective of the active clock census or mass signs. It can be reused in the twelve-active six-pair case; the finiteness below uses thirteen active rows.

Let \(z=c_6,\ x=c_7,\ h=a/2\). Both-new chronology makes \(h,a,z,x\) distinct and nonzero; in particular \(z,x\ne a\). The measured forward responses at \(h,z,x\) are \(F(t)=t^2(a-t)/a\ne0\). For a model \(P\in X\,K[X]_{\le4}\), let \(L(P)\) be the unique actual grade-five lift vanishing through the first six rows. The actual grade-four vector with model \(V_a=X^2(X-a)^2\) vanishes through row 7. Its primitive is exactly the anchored lift of \(P_a=JV_a\), where \(P_a(a)=a^5/30\ne0\), and vanishes at row 7 (even at 8).

Replace \(P\) by \(\widetilde P=P-P(a)P_a/P_a(a)=X(a-X)S(X)\), with \(\deg S\le3\). This preserves the seventh reading and the derivatives at 0 and \(a\), since \(P_a'\) vanishes there. The anchored correction on noncarriers is a quadratic \(T(C)F\): the coefficient of the other pure direction is zero from the literal two plateau reads and their independent fifth pivot, since \(\widetilde P(a)=0\). The row-4 read gives \(T(a)=0\). The zero reads at \(h,z\) show \(S(X)+XT(X)/a=(X-h)(X-z)(U+VX)\). At the two endpoints of interpolation,
\[
 P'(0)=a h z\,U,\qquad
 P'(a)=-a h(a-z)(U+aV).
\]
Hence the actual physical row-7 functional is
\[
 L(P)_7 =
 \frac{x(a-x)(x-h)(x-z)}{a^2h z(a-z)}
       \big[(a-x)(a-z)P'(0)-xz P'(a)\big].
\]
Every prefactor is nonzero by the distinctness and endpoint guards. Nothing is inferred at an unearned coincident seventh boundary.

In reflected physical coordinates \(Y=1-X\) the same proof gives row 11 of the anchored reversed lift \(R(Q)\), \(Q\in(1-X)K[X]_{\le4}\). Use \(v=1-c_{12},u=1-c_{11}\), width \(b\), and derivatives of \(Q(1-Y)\) at \(Y=0,b\). All reverse stages used are at grade at most five under the known order-ten weighted transpose. No reverse grade-ten square is used.

In the anchored monomial bases \(X^{i+1}\) and \((1-X)X^j\), \(0\le i,j\le4\), the exact mixed Gram of physical rows 7 through 11 is \(G=(1/[(i+j+2)(i+j+3)])\). Its inverse is \(210N\) with integer matrix `invG`. If \(L,R\) are the middle read matrices, \(G=L^T\operatorname{diag}(b_i)R\). Thus \(L G^{-1}R^T=\operatorname{diag}(b_i)^{-1}\), since \(G\) is symmetric and both matrices invertible. The pairing of physical left 7 with physical right 11 is zero.

Set
\[
 \ell_0=(a-x)(a-z),\quad\ell_1=-xz,\qquad
 r_0=(b-u)(b-v),\quad r_1=-uv.
\]
Drop the two **nonzero** prefactors and 210 to get the off-diagonal equation
\[
 \Psi=\ell_0r_0+T_4(a)\ell_1r_0+T_4(b)\ell_0r_1+
                  U_{4,4}(a,b)\ell_1r_1=0 .
\]
Here \(T_4(t)=1-32t+216t^2-480t^3+330t^4\), and the coefficient array of \(U_{4,4}\) is `uPoly` in ascending \(a\)-power then \(b\)-power. The derivative coefficient rows are \(1_{i=0}\), \((i+1)a^i\), \(1\), and \((1-b)^j-bj(1-b)^{j-1}\) (the \(j=0\) entry is 1). Pair them with \(N\) to obtain the functions. The \(5\)-by-\(5\) exact interpolation grid suffices for both bidegrees. The two extra clocks on either front enter symmetrically, so their physical order need not be decided here.

## 4. A characteristic-zero finite projection, not a mod-101 tableau argument

The four-distinct Hankel has degree at most six in \(b\), since each moment is quadratic in \(b\). Its constant and sixth coefficients, checked by degree-six interpolation in \(a\), are
\[
 [b^0]D=\frac{16-216a+1206a^2-3375a^3+4932a^4-3564a^5+990a^6}{1408264704000},
 \qquad
 [b^6]D=\frac{20-210a+910a^2-1995a^3+2303a^4-1323a^5+294a^6}{28449792000}.
\]
For the sixth coefficient use the moments of the leading coefficient of \(P_4\), \((X-a)(X-a/2)/2\). Both numerators retain degree modulo 101, and the finite receipt supplies a Bézout identity equal to 1 in that field. They are coprime over the rationals: a common primitive integer factor of positive degree would retain degree because both leading coefficients retain theirs. Thus **\(D(a,b)\) is not identically zero in \(b\) for any \(a\)** in any characteristic-zero extension, including the exceptional fibers of the next localization.

For four calibrations label the clocks \((a,h,d,e,t_1,t_2)\), the last two from the quadratic cofactor. The left extras are from indices \(2,3,4,5\) and right extras from \(0,1,4,5\) (zero-based). They cannot both include the opposite plateau, since that consumes two triples. There are \(6^2-3^2=27\) diagrams as an overcount. With \(h=e\) and three free labels at \(4,5,6\), the analogous lists \((2,4,5,6)\), \((0,4,5,6)\) give 27. In a mixed overlap \(a=e\), the triple is used at \(a\) by the literal left plateau and right half. Neither front can add the opposite plateau as a new label: both have only the three free labels for extras. The companion safely checks the larger lists \((2,4,5,6)\), \((4,5,6)\), giving 18 rather than 9 cases. The other mixed overlap is reflected and uses \((4,5,6)\), \((0,4,5,6)\), again 18. This retains arbitrary triple labels in the no-overlap and half-half cases and does not rely on chronological ordering of free roots.

Start with rational indeterminate \(a\). In the four-calibration case make \(D\) monic in \(b\) by inverting its leading coefficient. The resulting algebra of \(b\) is finite free of rank six in the monomial basis. The determinant of multiplication by \(\Delta\) is a rational function of \(a\), nonzero by the specialization below. Invert this scalar determinant so the multiplication adjugate inverts the element \(\Delta\). The displayed \(u,v\) are then in the localized algebra. Adjoin \(t_1\) by the monic \(X^2+uX+v\), and set \(t_2=-u-t_1\). The total algebra has a fixed monomial basis of rank twelve over the scalar parameter ring. Each actual layout whose \(a\) avoids the finitely many scalar denominators defines an evaluation into its coefficient field, choosing the actual two uncalibrated roots in either order.

For each overlap write \(b\) as the specified linear expression in \(a\); invert the determinant of the cubic cofactor solve. For the monic cubic \(g\), adjoin \(t_1\) by \(g(t_1)=0\), then \(t_2\) by the monic quadratic \((g(X)-g(t_1))/(X-t_1)\), and recover \(t_3\) by trace. This is finite free of rank six. At exceptional \(a\)'s of subsequent norms, one \(b\) is still fixed and the actual cubic pivot cannot fail by Section 2. No vertical continuous fiber hides in these overlap exceptions.

For each diagram take the **coefficient norm** of \(\Psi\), the determinant of multiplication in the fixed monomial basis. The companion gives exact witnesses that it is not identically zero: specialize \(a=2\) for four distinct calibrations and \(a=3\) for each overlap, then reduce coefficients modulo 101. The finite field is used on explicitly defined rational polynomial algebras, **not on unknown tableau coefficients**. The sample values need not be admissible (e.g. \(a=2\) need not satisfy the endpoint exclusions). Moment denominators are units mod 101. For four calibrations the Hankel leading coefficient specializes to 11, and an explicit inverse witness for \(\Delta\) makes its multiplication determinant a unit. For each overlap the specialized moment determinant is nonzero and the displayed monic cubic solves the moment equations. Explicit unit witnesses for \(\Psi\) cover all 90 diagrams in the corresponding rank-twelve or rank-six algebra. A unit has nonzero multiplication determinant even if the algebra is not a field and its monic polynomials have repeated factors. Since these algebras are finite free and the checked scalar denominators specialize to units, the determinants commute with specialization. Their nonzero reductions prove the rational functions are nonzero in characteristic zero.

For an actual layout either \(a\) is in the finitely many zeros of scalar denominators or its diagram norm vanishes there: otherwise \(\Psi\) is a unit under evaluation and cannot be zero. Thus \(a\) is among finitely many algebraic values uniformly across characteristic-zero fields. For four calibrations \(b\) has finitely many possibilities even on exceptional fibers by \(D(a,b)\not\equiv0\); the actual quadratic always has its proved-live pivot. For each overlap \(b\) is fixed by \(a\) and the actual cubic is uniquely fixed. Root permutations and physical clock assignments are finite. This proves the finite atlas without asserting feasibility or enumerating the norm roots.

## 5. Ordered-field support cut: no three cross-front pairs

In the both-new branch the actual forward and reverse grade-four vectors of models \(X^2(X-a)^2\) and \((1-X)^2(X-d)^2\) can pair only on physical rows 8,9,10. Their numerical product vanishes at either plateau: on noncarriers the actual left vector is \(c^2(c-a)^2+a(c-a)F\), and the reflected formula has its factor \((c-d)\). The common low-grade spaces allow two clock factors at total grade ten. If all possibly contributing inner clocks are a single label \(q\), insert \((X-q)^2\) to get numerical zero, but model integral
\[
 \int_0^1 [X(X-a)(1-X)(X-d)(X-q)]^2>0.
\]
The rational degree-five Gram is positive definite over any ordered field by rational positive-pivot elimination. Thus at least two distinct non-plateau inner clocks must contribute.

A cross-front pair is an ordinary pair with one occurrence on each front. Three cross-front pairs exhaust the three non-own-plateau occurrences on both fronts. If the triple is at neither plateau, the same three of four non-plateau labels are those pairs; the triple is wholly inner, giving only one possible contributing clock. If the triple is at a plateau, its third occurrence is inner and the sole remaining non-plateau pair fills the other two inner rows. The triple contributes zero at its plateau, again leaving only one clock. Thus three cross-front pairs are impossible over ordered fields. This cut is not used in the characteristic-zero finite projection.
