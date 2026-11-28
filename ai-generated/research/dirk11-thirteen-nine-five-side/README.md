# No five-dirty side in the normalized DIRK11/13 nine-label face

Under the established normalized rank and signed-support census, the
nine-active-dirty-label face cannot have five dirty rows before the first
interior clean row, nor five after the last interior clean row. The
surviving triples \((a,m,d)\) of dirty rows before, between, and after
the two interior clean rows are
\[
        (3,3,3),\ (3,2,4),\ (4,2,3),\ (4,1,4).
\]
The ordinary real DIRK11 stage interval **13–14** is unchanged.
This supersedes the [adjacent-only exclusion](../dirk11-thirteen-nine-adjacent/README.md)
on its two narrower profiles; that packet retains a distinct mixed
clean-gap proof. The zero- and one-active-dirty-label cases also remain.

We use the [nine-label virtual quadrature](../causal-profile-reduction/dirk-order11-thirteen-dirty-chronology.md)
and its [pure reverse grade-five clean block](../causal-profile-reduction/dirk-order11-thirteen-nine-backward-pure.md).
The scalar eliminations below are exact rational and finite quotient
proofs, not an end-to-end native port of the counted support or
resultant steps. No finite-field tableau search is used.

## An additional paid commutator test

Let \(e,f\) be the clean interior clocks in physical order, \(U\)
the cubic equal to the actual defect \(g\) on nine distinct dirty
stages, and \(h=U(c)-g\) the clean-supported grade-three column.
The seven macro sites of the virtual degree-ten rule are
\(0,e,f,1\) and the three distinct roots \(\rho\) of \(U\).
Their weights are nonzero. The grade-six virtual residual profile
is a multiple of
\[
  G(X)=X(462X^5-1260X^4+1260X^3-560X^2+105X-6),
\]
by the exact degree-ten scalar rule's five moment tests and
the zero at the origin. As in the adjacent proof, its value is
nonzero at every nonorigin macro site, including \(e,f\).
Put \(A_0=I(XU)\), \(A_1=I(X^2U)\) with \(IP(x)=\int_0^xP\).

Orient the longer side as the forward end first. If there are five
initial dirty stages, the dirty trace polynomial \(P_5\) of \(A(Ch)\)
is nonzero, has degree at most five, and vanishes at the five initial
dirty clocks, by the true \(E_5\) reading and inclusive causal cut.
The degree-at-most-six dirty trace of \(A(C(C-e)h)\) vanishes
at those same five clocks; it need not have only those roots.
It is thus an affine multiple of \(P_5\). At the roots of \(U\),
\(P_5(\rho)=A_0(\rho)\), while the higher trace has virtual residual
multiple fixed by its actual zero at \(e\). The necessary
coefficient determinant is
\[
              F(e)=G(e)D_0-\bigl(A_1(e)-e A_0(e)\bigr)D_1=0,
\]
where
\[
 \begin{split}
 D_0&=\det_{1,X,X^2}
 [\operatorname{rem}_{U} A_0,\operatorname{rem}_{U}(XA_0),\operatorname{rem}_{U} A_1],\\
 D_1&=\det_{1,X,X^2}
 [\operatorname{rem}_{U} A_0,\operatorname{rem}_{U}(XA_0),\operatorname{rem}_{U} G].
 \end{split}
\]
The \(-e A_0\) term cancels from the determinant as a column
multiple. This affine test does **not** require adjacency.

Make a second use of the same causal polynomial factor. The genuine
Volterra commutator \(R=CA-AC-A^2\) carries the actual \(Ch\in E_4\)
to \(F_6\), since the analytic identity \(XI-IX-I^2=0\)
has zero scalar profile. Its dirty trace has degree at most six
and is still zero at all five initial dirty stages, hence is an
affine multiple of \(P_5\). At \(e\), its first nonzero donor
coordinate is on the actual diagonal:
\[
                       (R Ch)_e=-A_{ee}^{\,2} e U(e).
\]
If \(A_{ee}\ne0\), the virtual correction coefficient is
nonzero, and thus the virtual trace is a *nonzero*
multiple of \(G(\rho)\). Dividing only by that coefficient
gives \(D_1=0\). If \(A_{ee}=0\), the true
forward primitive already gives \(A_0(e)=A_{ee}eU(e)=0\).
The combined additional condition is consequently
\[
                            A_0(e)D_1=0 .
\]
The diagonal-zero case is retained, not discarded.

For the mirror with five late dirty rows use the weighted true
backward action and \(y=1-c\). The corresponding commutator
is \(R^\mathsf T\): writing \(N=A^\mathsf T,\ Y=I-C\),
one has \(YN-NY-N^2=R^\mathsf T\). Acting on
\(b(1-c)h\) gives a terminal-zero row annihilating \(E_4\),
by the same paid \(R(E_4)\subset F_6\) and the exact grade-ten
pairing. Its dirty trace after division by the nonzero \(b_i\)
is degree at most six from its \(g{\cal P}_1\) annihilators.
The virtual grade-six shape is \(G(1-X)\) by pairing with
the five low moments and vanishing at the true terminal.
The reflected chronological pivot is the same literal square
with the roles of \(e,f\) exchanged. This justifies the
same two tests on the mirrored coordinates without invoking
any order statement for a transposed RK method.

## Exact scalar elimination and all guards

Write \(s=e+f,\ p=ef,\ C_2=X^2-sX+p\) and take the same shifted
\(J_4,J_5\) pencil as in the adjacent proof. Write \(q_j,r_j\) for
quotient and remainder modulo \(C_2\) and
\(r_j=r_{j0}+r_{j1}X\). The remainder determinant
\(D=\operatorname{prim}(r_{40}r_{51}-r_{41}r_{50})\) in
\(s,p\) must vanish. The two \(J\)'s are coprime; at least one
of \(r_{40},r_{41}\) must be nonzero.

On the zero-slope chart \(r_{41}=0\), one has \(r_{40}\ne0\) and hence
\(r_{51}=0\). Note the identity
\(r_{41}=14(s-1)(-6p+3s^2-3s+1)\).
If \(s=1\), the equation for \(p\) becomes
\(132p^2-36p+2=0\). Otherwise
\(p=(3s^2-3s+1)/6\) and \(s\) is a zero of
\(99s^4-396s^3+573s^2-354s+79\). In both exact
number-algebra calculations, the affine condition alone is
coprime to the clean quadratic \(C_2\) in \(e\).
They use the scaling \(U=r_{40}q_5-r_{50}q_4\).

For \(r_{41}\ne0\), scale \(U=r_{41}q_5-r_{51}q_4\).
One can clear all powers of its leading coefficient
\(132r_{41}\) in the remainder determinant \(F\) as follows:
compute \(D_0,D_1\) first with a formal monic cubic
\(X^3+uX^2+vX+w\); substitute the three lower
coordinates divided by \(132r_{41}\), and homogenize
all terms to a common power of that unit. Then reduce
\(F(e)\) modulo \(C_2(e)\) to \(A(s,p)+eB(s,p)\).
The conjugate norm \(A^2+sAB+pB^2\) is a necessary equation;
reduce it modulo \(D\) and clear denominators to a primitive
integer polynomial \(N_F(s,p)\).

The degree-188 resultant of \(D,N_F\) in \(p\) has
factor degrees and multiplicities
\[
       (1,28),(4,1),(4,2),(4,14),(6,2),(10,2),(60,1).
\]
For each factor of degree below 60, compute the exact gcd
of \(D,N_F\) in \(p\) modulo that factor. The gcd divides
at least one of the explicit guards \(r_{41}\), \(p\), \(1-s+p\),
\(U(0)\), or \(\operatorname{Res}_X(G,C_2)\), respectively
denying zero slope, collision with origin or terminal,
virtual cubic root at origin, or zero \(G\) at a clean clock.
Every guard is known nonzero on this chart. All rational
quotient inversions are checked as actual division; this is
not a generic discarding of low-degree factors.

## The finite-free rank lift at 23

On the only remaining factor \(R_{60}(s)\) the finite rational
model has monic relations \(R_{60}(s)\), \(D(s,p)\) in \(p\),
and \(e^2-se+p\) in \(e\). Over \(\mathbb Z_{(23)}\) the two
leading coefficients being normalized are units, so this is
finite free of rank \(60\cdot4\cdot2=480\).
The relevant extra equations are the already cleared \(F,N_F\)
and the pivot product \(A_0(e)D_1\). Replace remainder columns in
the last equality by their polynomial pseudo-remainders to
clear any leading coefficient of \(U\); integration denominators
are units at 23. This is harmless also on every tested common
component modulo 23 because \(r_{41}\) is nonzero there.

After exact prime-23 specialization, \(R_{60}\) has six
different irreducible factors of degrees \(1,2,14,14,14,15\).
In each component \(D,N_F\) have a linear gcd determining \(p\).
The nonzero coefficient of \(e\) in \(F\) determines \(e\),
and the replay checks its clean quadratic. It then verifies
**both** \(A_0(e)\ne0\) and \(D_1\ne0\) in that field.
Thus the three extra equations generate the unit ideal
modulo 23 in the rank-480 model. A surjective multiplication
map modulo 23 has a full-rank minor nonzero over
\(\mathbb Q\), so the corresponding rational ideal is the
unit ideal. This excludes all characteristic-zero
specializations, without any assumption that a candidate
tableau or its root parameters could first be reduced at 23.

Run `python3 -B replay.py` with SymPy for the exact guard,
factor and rank transcript. No numerical root approximation
or real-root interval decision is used in the elimination.

The reviewed `DIRKOrderElevenVolterraCuts` module separately proves the
actual grade-six forward cut, literal backward pivot, order-eleven
weighted annihilator payment, and terminal-column debit. Its
[typed audit](lean-audit.txt) does not claim a Lean port of the
rational resultant or finite-algebra computation.
