# Finitely many macro geometries for the balanced DIRK11/13 chart (4,1,4)

This exact reduction does **not** exclude the chart or improve the
stage interval **13–14**. It applies to a normalized real order-eleven
thirteen-stage lower triangular tableau in the nine-active-dirty-label
case, with four dirty stages before the first interior clean, one
between the two interior clean stages, and four after the last.
It reduces the possible seven-site virtual abscissae to a finite
algebraic set, **including zero-leading-factor branches**.
The [general balanced hull setup](../causal-profile-reduction/dirk-order11-thirteen-nine-balanced-hulls.md)
and [five-side elimination](../dirk11-thirteen-nine-five-side/README.md)
give the literal paid entries used below.

Let \(e,f\) be the two interior clean clocks in physical order and
\(z\) the middle dirty clock. The cubic \(U\) on the nine dirty
rows and its monic associate \(U_{\rm m}\) have the same three
roots \(\rho\). The seven-site rule has nonzero masses \(m_\rho\)
there. All nine literal dirty clocks are distinct, and none is
a root of \(U\), in particular \(U(z)\ne0\). The cleaned macro
geometry can use \(U_{\rm m}\) without loss of generality:
each primitive and grade-six projection scales linearly with \(U\),
each quotient below is invariant or then normalized by its
leading coefficient, and each Volterra ratio is scale invariant.

## Two affine equations in the literal middle clock

Use the earlier conventions for \(A_0,A_1,B_0,B_1,H_L,H_R\),
including the true causal grade-six coefficient from the zero
at the opposite clean cut. Let \(G^\leftarrow=G(1-X)\).
The generic algebraic formulas here are written first when
\(A_0(\rho)B_0(\rho)\ne0\) at all three virtual sites and the
indicated quadratic leading coefficients are nonzero.
The guard construction below explicitly includes all other cases.

In the cubic algebra modulo \(U_{\rm m}\), write the reduced quadratic
representatives of
\[
 Q_L=H_L/A_0,\quad Q_R=H_R/B_0,\quad
 M(\rho)=m_\rho U'(\rho) A_0(\rho) B_0(\rho).
\]
Write \(q_L,q_R,m_2\) for their \(X^2\) coefficients and
\(Q_L^*=Q_L/q_L,\ Q_R^*=Q_R/q_R,\ M^*=M/m_2\) for their monic
versions. In the fixed geometry, these are polynomials of degree
exactly two.

From the [literal hull polynomials](../causal-profile-reduction/dirk-order11-thirteen-nine-balanced-hulls.md)
one has \(\ell_L Q_L\equiv(X-z)k_L\pmod{U_{\rm m}}\) with
\(\ell_L,k_L\) affine, \(\ell_L\ne0\), and the mirror condition.
Indeed multiply the virtual equations involving \(L\) by
\(\ell_L\) and cancel the live \(A_0\). Evaluating the reduced
left side at \(z\) gives
\[
       Q_L(z)\ell_L(z)-q_L\ell_L' U_{\rm m}(z)=0.
\]
If \(\ell_L(z)=0\) then \(\ell_L'=0\), impossible, since
\(q_L U_{\rm m}(z)\ne0\). Thus both \(\ell\)'s can be
normalized to have value 1 at \(z\), and the resulting scalar
polynomials are
\[
 \ell_L=1+\frac{Q_L^*(z)}{U_{\rm m}(z)}(X-z),\qquad
 \ell_R=1+\frac{Q_R^*(z)}{U_{\rm m}(z)}(X-z).
\]
This rescaling for scalar ratios does not assert that the corresponding
monic actual dirty nodal hulls have been rescaled.

The full dirty barycentric equation at the virtual sites makes
\(\ell_L\ell_R\) proportional to \(\operatorname{rem}_{U_{\rm m}}[(X-z)M^*]\).
For instance multiply \(A_0 B_0=L R\,\ell_L\ell_R\) by
\(m_\rho U'(\rho)(\rho-z)\) and use the actual nodal hull
\(V=L(X-z)R\). Its global \(\kappa\) absorbs the two scalar
normalizations of \(\ell_L,\ell_R\). The polynomial remainder is
\((X-z)M^*(X)-U_{\rm m}(X)\), which takes value \(-U_{\rm m}(z)\)
at \(z\). Compare first and second \(X-z\) coefficients to obtain
\[
 \begin{split}
 L_0(z)&=0,\qquad L_0=Q_L^*+Q_R^*+M^*-U_{\rm m}',\\
 Q_L^*(z)Q_R^*(z)&=U_{\rm m}(z)
                 \bigl(U_{\rm m}''(z)/2-(M^*)'(z)\bigr).
 \end{split}
\]
The first polynomial is affine because the leading quadratic
coefficients cancel. The second equality is a cubic condition
after cancellation of its quartic terms.

The actual shared middle-diagonal equality gives another **affine**
polynomial. Let \(T_L=\operatorname{rem}_{U_{\rm m}}(G/A_0)\)
and \(T_R=\operatorname{rem}_{U_{\rm m}}(G^\leftarrow/B_0)\).
With the prior actual clean diagonals
\(d_e=A_0(e)/(eU(e)),\,d_f=B_0(f)/[(1-f)U(f)]\), put
\[
 \theta_e=-d_e^2 eU(e)/G(e),\qquad
 \theta_f=-d_f^2(1-f)U(f)/G^\leftarrow(f).
\]
The normalized Volterra quotient at \(z\) is
\(\theta_e[T_L(z)-(T_L)_2 Q_L^*(z)]\) on the left: reduce
\(T_L\ell_L\) modulo \(U_{\rm m}\) and subtract its degree-three term,
then evaluate at \(z\). The right formula is the same with \(T_R,Q_R^*\).
Both brackets are affine. The two actual diagonal calculations
therefore imply \(L_1(z)=0\), where
\[
 L_1=\theta_e\bigl(T_L-(T_L)_2Q_L^*\bigr)
 -\theta_f\bigl(T_R-(T_R)_2Q_R^*\bigr)-2X+e+f-d_f+d_e .
\]
No nonzero-diagonal assumption enters; \(\theta_e\) or
\(\theta_f\) is allowed zero. In particular the two coefficient
vectors of \(L_0,L_1\) must have zero determinant \(\Delta\),
even if either \(X\)-coefficient is zero.

## A nonzero norm that also catches all failed guards

Take \(s=e+f,\ p=ef\), and the monic clean quadratic \(X^2-sX+p\).
As in the five-side proof let \(q_i,r_i\) be the quotients and
remainders of the fixed \(J_i\) for that quadratic, and
\(D=\operatorname{prim}(r_{40}r_{51}-r_{41}r_{50})\).
Its leading coefficient in \(p\) is the nonzero constant 2772.
If \(r_{41}=0\), the exact split from the preceding proof applies:
\(s=1\) with \(132p^2-36p+2=0\), or a root of the stated quartic
\(99s^4-396s^3+573s^2-354s+79\) with
\(p=(3s^2-3s+1)/6\). This is already a finite possible macro set;
no exclusion via the five-side-specific affine test is imported here.

For \(r_{41}\ne0\), all expressions can be calculated with the
fixed scaled cubic \(r_{41}q_5-r_{51}q_4\) and its monic associate.
The ordinary virtual mass satisfies
\[
 m_\rho U'(\rho)
 =\frac{\int_0^1 x(1-x)(x^2-sx+p)\, U(x)/(x-\rho)\,dx}
        {\rho(1-\rho)(\rho^2-s\rho+p)} .
\]
Use the synthetic quotient
\(U(X)/(X-\rho)=u_3X^2+(u_2+u_3\rho)X+(u_1+u_2\rho+u_3\rho^2)\)
at each root to define this expression in the cubic algebra,
without choosing an order of its roots.

Work over the finite free rank-eight algebra
\[
    {\cal A}=\mathbb Q[S][P,E]/(D(S,P)/2772,\ E^2-SE+P).
\]
All inverses in the scalar formulas have a denominator-clearing
implementation: an inverse modulo the monic cubic is its
three-dimensional multiplication matrix's adjugate divided by
its determinant. Represent arithmetic expressions as pairs of
polynomial numerators and denominators in \({\cal A}\), using
the usual cross-product formulas, but without cancelling
or requiring that a divisor is a unit in \({\cal A}\).
Each time an explicit division is used, append the numerator
of its divisor to a polynomial product \(\Gamma\).
This includes the cubic normalization, all scalar/weighted
primitive denominators and cubic inverse determinants, and the
three leading coefficients \(q_L,q_R,m_2\).
In these terms every displayed calculation defines
polynomials regardless of where a specialization may make a
guard vanish. The cleared numerator of \(\Delta\) is denoted
\(\widetilde\Delta\). An actual candidate either has a first
failed guard (so \(\Gamma=0\)) or all guards evaluate nonzero
(in which case the calculations are valid and
\(\widetilde\Delta=0\)). Thus the single polynomial
\(\Gamma\widetilde\Delta\) vanishes at **every** relevant
candidate, not just a generic subchart.

The multiplication determinant of this element in \({\cal A}\)
is a polynomial \(N(S)\) over \(\mathbb Q\). It is
**not identically zero**: at the directly verified specialization
\(S=7\) modulo 19, the quartic defining \(P\) is the
irreducible \(P^4-8P^3+3P^2+P-6\). Use the full quadratic
\(E^2-7E+P\) over that field. Every one of the algorithm's
division guards is a unit, verified by actual inversions,
and the quadratic norm of the computed line determinant is
\(3P^3-6P^2+8P+1\ne0\) in the quartic field.
Thus both \(\Gamma,\widetilde\Delta\) specialize to units in
the entire eight-dimensional algebra. Only rational constants
with denominator prime to 19 were used before the specialization.
Consequently \(N\) has a nonzero value under this reduction
and is nonzero over \(\mathbb Q\).

For an actual macro geometry, if \(N(s)\ne0\) the specialized
multiplication map is invertible, whereas evaluation at the
candidate sends its multiplier to zero. Contradiction. So \(s\)
is a root of a fixed nonzero polynomial. Each such \(s\)
gives at most four \(p\)'s and at most two values of \(e\) per
\(p\); \(f=s-e\) and the pencil parameter are determined.
Together with the zero-slope list, this proves a finite set of
algebraic macro geometries, even for candidates meeting a
division or leading-coefficient degeneracy. The polynomial
is given by the displayed determinant construction, not expanded
to a coefficient list. Neither its roots nor the remaining
physical tableau parameters have been excluded.

Run `python3 -B replay.py` with SymPy to replay the good
specialization. This is an exact check of a nonzero polynomial,
not a finite-field tableau construction or an unsupported
inference about reduction of a real point.
