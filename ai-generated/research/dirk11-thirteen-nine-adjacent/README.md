# Excluding adjacent interior clean stages in the nine-label DIRK11/13 face

The real stage interval still is **13–14**. This eliminates **two**
normalized nine-active-dirty-clock chronological profiles, namely
\((5,0,4)\) and \((4,0,5)\). The counts refer to the number of dirty
stages before the first interior clean, between the interior clean
stages, and after the last interior clean, in physical order.
The six nonadjacent nine-label profiles and the zero- and one-active-
dirty-label charts are not excluded here.

The inputs are the
[signed cubic census](../causal-profile-reduction/dirk-order11-thirteen-signed-cubic-census.md),
[virtual quadrature and chronology](../causal-profile-reduction/dirk-order11-thirteen-dirty-chronology.md),
and
[pure reverse grade-five block](../causal-profile-reduction/dirk-order11-thirteen-nine-backward-pure.md).
All weighted reads below are of the literal tableau; no full RK order
for the weighted transpose is assumed. The proof and scalar replay are
exact; this packet does not claim a full native Lean elimination.

## Two independent scalar gates

Let \(e,f\) denote the interior clean clocks in physical order,
and \(U\) the cubic equalling the actual cubic defect \(g\) on
the nine dirty rows. Hence \(h=U(c)-g\) is supported on the four
clean rows \(0,e,f,1\). The virtual degree-ten exact quadrature
uses those four sites and the three distinct roots \(\rho\) of
\(U\), with nonzero macro weights \(m_\rho\).
Neither a root \(\rho\) nor \(e,f\) coincides with an endpoint,
and \(U(e)U(f)\ne0\). Dirty numerical clocks may coincide with
clean ones but never with roots of \(U\).

Write \(I P(x)=\int_0^x P\), \(I^\leftarrow P(x)=\int_x^1 P\)
and put \(A_0=I(XU)\), \(A_1=I(X^2U)\), and
\(B_0=I^\leftarrow((1-X)U)\).
The two-clean-block proof gives the necessary adjacent-moment gate
\[
                 \sum_\rho m_\rho A_0(\rho)B_0(\rho)=0.
\]
It comes from \(\beta((1-C)h)\, A^2 (Ch)\) at total grade ten.
With no intervening dirties, only the two physical clean coordinates
can contribute to that cut. The actual reverse grade-five and forward
grade-five primitives compute exactly the two clean terms of the
virtual degree-ten rule; comparison gives the missing three-root sum.

Now orient the face with five dirties on the forward side, the other
case being the paid backward mirror. Set
\[
 G(X)=X(462X^5-1260X^4+1260X^3-560X^2+105X-6).
\]
The parenthetical polynomial is orthogonal to degrees zero through
four for \(x\,dx\) on \([0,1]\); its five integrals verify this
directly. The virtual grade-six residual vectors have origin entry
zero and kill the five exact moments on six other macro sites.
The vector \(G\) evaluated on those sites spans their same
one-dimensional barycentric kernel by degree-ten exactness.
It is nonzero as a vector because a nonzero polynomial of degree six
cannot vanish at those six sites *and* the origin. Every coordinate
of the moment kernel is nonzero, so in particular \(G(e)\ne0\).

The two actual forward traces \(A(Ch)|_{\rm dirty}=P_5(c)\) and
\(A(C(C-e)h)|_{\rm dirty}=P_6(c)\) have degrees at most five
and six. Both vanish at the five initial dirty labels by causality.
The first trace is nonzero by the prior clean-support separation
proof; therefore their quotient is affine (including the zero case
for the second numerator). On the virtual roots, the pure
forward grade-five profile gives \(P_5(\rho)=A_0(\rho)\),
and the grade-six virtual profile gives
\[
       P_6(\rho)=A_1(\rho)-e A_0(\rho)
          -\frac{A_1(e)-e A_0(e)}{G(e)} G(\rho).
\]
Here \(A(C(C-e)h)\) is zero at the literal earlier clean row \(e\),
because the input is supported only at \(f,1\). This determines the
grade-six residual multiple of \(G\). The virtual read of ordinary
polynomials is plain evaluation, even if such a profile is only
used as part of a true tree-weight decomposition.

Define
\[
       K(X)=G(e)(A_1(X)-eA_0(X))-(A_1(e)-eA_0(e))G(X).
\]
The quotient condition requires the coefficient determinant
\[
 \det_{1,X,X^2}
       [\ \operatorname{rem}_U A_0,\
          \operatorname{rem}_U (X A_0),\
          \operatorname{rem}_U K\ ]=0 .
\]
This follows by evaluating the three columns at the three simple
roots of \(U\), where the last column is an affine multiple of the
first. No pointwise division by \(A_0(\rho)\) is used by the check.

For the mirror case apply the same derivation to the literal weighted
backward reads with clock \(y=1-c\) and samples \(1-f,1-e\).
The order-four and order-five error rows vanish on all clean
coordinates by pure reverse grade five. At grade six the error row
is in the terminal-zero \(\operatorname{Ann}E_4\); pairing with
\(g{\cal P}_1(c)\) gives a degree-at-most-six polynomial for its dirty
coordinates divided by the nonzero ordinary dirty weights. The
virtual residue transfer then makes its projected correction a
multiple of \(G(1-c)\), by the exact five moments and its zero at
the true terminal. The nonzero first polynomial under the mirrored
cut is the previously proved backward dirty-trace separation.
Thus the same determinant test holds with all variables reflected.
The Jacobi pencil and the adjacent-moment condition are preserved
under that change of variables.

## Denominator-cleared tests

Put \(s=e+f,\ p=ef\) and \(C(X)=X^2-sX+p\). Write the exact
Jacobi quotient
\[
   (X-e)(X-f)U \ \propto\ J_5+\lambda J_4,\quad
   J_4=42X^4-84X^3+56X^2-14X+1,\quad
   J_5=(2X-1)(66X^4-132X^3+84X^2-18X+1).
\]
In the replay, \(q_j,r_j\) are the quotient and remainder of
\(J_j\) upon division by \(C\), and \(r_j=r_{j0}+r_{j1}X\).
Their remainder determinant \(D\) is the primitive part of
\(r_{40}r_{51}-r_{41}r_{50}\), of degree four in \(p\) with
constant leading coefficient 2772. It must vanish.
Since \(J_4,J_5\) are coprime, not both \(r_{40},r_{41}\)
can be zero at a candidate. In either chart \(d=r_{4i}\ne0\),
one may replace \(U\) by its nonzero scaling
\(d q_5-r_{5i} q_4\). Both tests are homogeneous in \(U\).

To check the adjacent moment without splitting a cubic, let
\[
 F=A_0 B_0/[X(1-X)],\quad
 \mu_k=\int_0^1 x^{k+1}(1-x)U(x)\,dx.
\]
The quotient defining \(F\) is a polynomial, because the two
primitives vanish at their respective endpoints. The virtual
quadrature is exact through degree ten; the three-root condition
is equivalent to \(\int A_0B_0\) equalling the sum of its two
clean contributions. By ordinary Lagrange interpolation the
contribution at \(e\) is
\(F(e)\,(\mu_1-f\mu_0)/[(e-f)U(e)]\), and the
contribution at \(f\) interchanges \(e,f\). Multiply by
\(U(e)U(f)\). The resulting polynomial equality uses just the
linear coefficient of the remainder of
\(F(X)U(s-X)(\mu_1-\mu_0(s-X))\) modulo \(C\), since its
divided difference at \(e,f\) is that coefficient.
Let \(S_i\) be the calculated condition, reduced modulo \(D\) and
cleared to a primitive integer polynomial for chart \(i\).

The exact rational resultant in \(p\) of \(D,S_0\) is coprime
to that of \(D,r_{41}\). Thus when \(r_{41}=0\) chart 0 gives
no solution. The resultant of \(D,S_1\) factors, up to a nonzero
constant, as
\[
   (s-1)^8(99s^4-396s^3+573s^2-354s+79)^4 R_{36}(s).
\]
At \(s=1\) one has \(r_{41}=0\) identically. Modulo the displayed
quartic, the exact Euclidean algorithm on \(D,S_1\) in \(p\)
gives a monic linear gcd dividing \(r_{41}\). Its coefficient
inversions have actual checked products, so this common-root
exclusion is valid under any embedding of that quotient. Both
low factors are therefore impossible on chart 1. The residual
polynomial \(R_{36}\) is reconstructed by exact division; the
proof does not require that it be irreducible over \(\mathbb Q\).

## Why the reduction modulo 19 excludes characteristic zero

After excluding the low factors, the exact candidate is a point of
the finite free rational-coordinate algebra defined by monic
\(R_{36}(s),D(s,p),e^2-se+p\), of rank \(36\cdot4\cdot2=288\).
Use the finite **free** model over \(\mathbb Z_{(19)}\);
leading coefficients of both monic normalizations are units
at 19. The two further equations are \(S_1=0\) and the affine
determinant. Treat its three columns as polynomial
pseudo-remainders to clear the leading coefficient of \(U\).
The integration denominators here are units at 19.
At every tested common-root branch modulo 19 the leading
coefficient of \(U\) is also a unit, so the ordinary remainder
checks differ from the pseudo-remainders only by invertible
column scales.

The [exact replay](replay.py) finds two distinct irreducible
factors of degrees 2 and 34 modulo 19. In each resultant
factor's coefficient field the Euclidean gcd in \(p\) of
\(D,S_1\) is linear. After substituting this \(p\), the norm
of the affine determinant under \(e^2-se+p\) is nonzero in
that coefficient field. This verifies that the determinant
is invertible even if that last quadratic is split.
By the Chinese remainder theorem, the two equations generate
the unit ideal modulo 19 in the rank-288 free algebra.
The associated multiplication map from two copies of the algebra
to one copy therefore has full row rank modulo 19. A maximal
minor nonzero modulo 19 is nonzero over \(\mathbb Q\), so the
same map has full row rank in characteristic zero.
Any proposed characteristic-zero specialization satisfying
both equations would send its unit to zero, impossible.
This is **not** an inference from the absence of rational or
real points reducing unconditionally to \(\mathbf F_{19}\).

Reproduce with `python3 -B replay.py` (SymPy; exact arithmetic
only). The [transcript](replay.log) records the guard and finite
quotient checks. Ordered-field or real assumptions occur in the
prior virtual quadrature construction, not in the displayed
finite quotient contradiction.
