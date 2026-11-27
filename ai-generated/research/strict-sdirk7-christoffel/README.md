# An order-seven Christoffel obstruction over the rationals

This packet rules out **two distinct active zeros of the virtual cubic defect**
in the [seven-distinct-active, two-zero-weight chart](../strict-sdirk7-two-ghost/README.md).
Neither helper clock, the fourth reverse read clock, nor any symmetry is fixed.
It does not rule out one active zero, all-active or repeated-clock methods,
or the whole nine-stage rational problem.

The key arithmetic fact is independent of Runge–Kutta methods:
the degree-three uniform Christoffel–Darboux kernel for the interval
\([-1,1]\) does not vanish at **any pair of finite rational arguments**,
even those outside the interval. Its proof uses a rational rank-zero
elliptic curve, not a bounded rational search.

## From five defect support sites to the kernel

Scale the rational reflected clocks to the centered interval \([-1,1]\).
The seven nonzero quadrature weights \(b_i\) pay the uniform moments
through degree six. Write \(P\) for their square-free node polynomial and
\(K_i=b_iP'(y_i)\). The rank-one defect has the virtual form
\[
V_i=W(y_i)L(y_i)/K_i,\qquad D_i=W(y_i)/P'(y_i)
\]
for affine \(W,L\). This form and the paid moments follow from the two-zero
ingress; affine coordinate change preserves the assertions up to nonzero
scales. The additional claims here use only that virtual form and its paid
relations
\[
 \sum_i b_i y_i^j V_i=0\quad(0\le j\le3),\quad
 \sum_i b_i V_i^2=0,\quad
 \sum_i D_i V_i=0,\quad
 \sum_i D_i y_i^j=0\quad(0\le j\le4).
\]

If \(V\) has distinct zeros \(e,f\) among the active nodes, its support
has size five, \(W(e)=L(f)=0\) after relabeling, and \(D_f\ne0\).
On the five support coordinates the row \(bV\) is nonzero. Its annihilator
has dimension four and contains the four-dimensional (distinct clocks)
space of cubic polynomial evaluations. Isotropy also places \(V\) in
that annihilator, so \(V_i=g(y_i)\) on its support for a degree-at-most-three
polynomial \(g\). The rank step is native in
[SDIRKSevenChristoffelScalar](../../lean/RKCert/Research/SDIRKSevenChristoffelScalar.lean).
Pair \(D\) with \(g\). Since \(D_e=0\) and \(D\) pays both \(V\) and
the whole cubic polynomial space, this gives \(D_f g(f)=0\), hence
\(g(f)=0\). For every cubic polynomial \(h\), the original seven-site
quadrature identity now gives
\[
I(gh)=b_e g(e) h(e),\qquad
I(q)=\tfrac12\int_{-1}^1 q(X)\,dX.
\]
Here \(g(e)\ne0\), since otherwise the nondegenerate rational uniform
cubic form implies \(g=0\). Writing \(P_j\) for Legendre polynomials
(\(P_0=1,P_1=X,P_2=(3X^2-1)/2,P_3=(5X^3-3X)/2\)), we obtain
\[
 \mathcal K(e,X)=\sum_{j=0}^3 (2j+1) P_j(e)P_j(X),\quad
 g(X)=b_e g(e)\mathcal K(e,X).
\]
Consequently \(\mathcal K(e,f)=0\) and \(b_e=1/\mathcal K(e,e)\).
The first equality is rationally impossible by the arithmetic below.

## Linear one-zero criterion when \(W\) vanishes at an active site

Let \(W(e)=0\) at an active clock, and restrict all vectors to
the other six sites \(S\). On \(S\), the two columns \(D/b\) and
\(YD/b\) are in the weighted orthogonal complement of cubic
polynomial evaluations by the degree-four \(D\) moments and
\(D_e=0\). They are independent, because all \(D_i\) on \(S\)
are nonzero and the clocks are distinct; hence they span that
two-dimensional complement. A virtual defect on \(S\)
satisfying both \(D\)-payments is a nonzero radical vector of
that complement. In the nondegenerate ambient six-site form
its radical is the same as the restricted cubic space radical.
The cubic Gram matrix is the invertible uniform cubic form
minus the single evaluation mass at \(e\). Its determinant
vanishes exactly when \(b_e\mathcal K(e,e)=1\), by the
rank-one determinant lemma. The radical is then the line
spanned by \(\mathcal K(e,\cdot)\).

Conversely if \(W(e)=0\) and \(b_e=1/\mathcal K(e,e)\), set
\(V_e=0,\ V_i=\mathcal K(e,y_i)\) on \(S\). The reproducing
identity gives cubic orthogonality and isotropy directly;
\(D_e=0\) and the degree-four \(D\) moments give both \(D\)
and \(DY\) payments. Thus this weight equality is **equivalent**
to the Gram condition on the stated stratum. The arithmetic
below guarantees the other six components are nonzero over
\(\mathbb Q\). For fixed rational \(e\), the additional weight
condition is linear in any unfixed factor of the node polynomial:
\(I(P/(X-e))=P'(e)/\mathcal K(e,e)\) in the same centered coordinate.
It gives a rational linear hull test, not a chronological
completion or a rational tableau.

This stratum is actually used by the earlier
[asymmetric finite control](../strict-sdirk7-two-ghost/f19-affine-zero-control.json).
Its reflected clock \(e=16\) normalizes to \(17\bmod 19\);
\(b_e=11\) and \(\mathcal K(17,17)=7\bmod19\).
The finite arithmetic is checked in the new native module;
the actual tableau and all 85 order conditions were checked
in the earlier packet.

## The kernel has no finite rational zero

Let \(p=ef,\ s=e+f\). Expanding \(4\mathcal K(e,f)=0\) gives
\[
 15(7p+1)s^2=(5p+3)(35p^2+30p+3).
\]
The right side equals \(-64/49\) at \(p=-1/7\), so \(r=7p+1\ne0\).
The native change of coordinates
\[
 X=-105(5p+3)/r,\qquad Y=12600s/r
\]
then gives \(E:Y^2=X(X^2+1350X+23625)\). Its 2-isogenous curve is
\(E':Y^2=X(X^2-2700X+1728000)\); both are nonsingular.
For the classical two-isogeny rank formula, see
[Dixit, Murty and Pathak, §2](https://www.imsc.res.in/~anupdixit/rankproblem.pdf).
Use the homomorphism \(\alpha(O)=1,\alpha((0,0))=[b]\),
and \(\alpha((x,y))=[x]\) on a curve \(y^2=x(x^2+a x+b)\).
The signed square-free divisor classes \(d\mid b\) can be in its image
only when
\[
 N^2=d m^4+a m^2 n^2+(b/d)n^4
\]
has a solution with coprime integral \(m,n\). For any ordinary point
this equation follows by \(x=d(m/n)^2\) in lowest terms and
\(N=y n^3/(dm)\), which is integral since its square is integral.
The prime support bound follows by parity of valuation of the curve
equation at each prime not dividing \(b\); negative \(v_\ell(x)\)
gives \(v_\ell(x^3)\), positive \(v_\ell(x)\) with \(\ell\nmid b\)
gives \(v_\ell(bx)\). The identity and two-torsion point are included
directly. In any excluded modulus \(\ell^k\), coprimality makes at
least one of \(m,n\) a unit; dividing by its fourth power gives one
of the two checked affine charts. Thus there is no lost projective
or denominator case.

For \(E\), the torsion class is \([105]\) and the signed square-free
class representatives modulo it are \(1,-15,-5,-3,-1,3,5,15\).
The seven nonidentity representatives are ruled out modulo
\(27,16,256,16,16,256,16\), respectively. On \(E'\), negative \(X\)
has a negative right side, so only positive classes need consideration.
The torsion class is \([30]\) and representatives are \(1,3,5,15\),
with the last three ruled out modulo \(625,81,27\). The native finite
gate checks both normalized unit charts in each row, and
[check-descent.py](check-descent.py) independently checks class coverage,
both charts and good-reduction counts using only standard Python.

Thus \(\#\operatorname{im}\alpha_E=\#\operatorname{im}\alpha_{E'}=2\).
The two-isogeny index formula
\(2^{\operatorname{rank}E}=\#\operatorname{im}\alpha_E\#
\operatorname{im}\alpha_{E'}/4\) gives rank zero.
The checked good reductions have 6 and 16 points at 11 and 17.
Injectivity on prime-to-reduction-characteristic torsion, applied at
both primes, gives torsion of order dividing 2. Hence \((0,0)\)
is the only affine rational point of \(E\).
It would require \(p=-3/5,s=0\), giving \(e^2=3/5\),
which is impossible over \(\mathbb Q\) (equivalently \((5e)^2=15\)).
The native theorem verifies the change of coordinates and this last step.
The use of the classical elliptic rank and torsion theorems and the
original graded HasOrder ingress are mathematical proofs, not claimed
as native Lean wrappers.

## Replay

Run the following from this directory:

    python check-descent.py

The native module and typed audit were checked using stock Lean 4.36.0
with the repository's usual Mathlib dependencies. No axioms are added
for the elliptic step.
