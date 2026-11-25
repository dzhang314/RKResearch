# Necessary conditions for a five-stage rational strict SDIRK method of order five

If a five-stage rational strict SDIRK tableau has order five, every
output weight is nonzero, exactly one weight is negative, and
\(-15\prod_i b_i\) is a rational square. These are necessary conditions
only; they do not rule out five stages.

## The paid quadratic defect

For any rational order-five tableau with \(\mathbf c\coloneqq A\mathbf 1\)
write
\[
\mathbf q\coloneqq A\mathbf c-\mathbf c^{\odot2}/2,\qquad
\langle\mathbf u,\mathbf v\rangle_b\coloneqq
\mathbf b\cdot(\mathbf u\odot\mathbf v).
\]
The reviewed rooted-tree conditions give
\(\langle\mathbf q,\mathbf c^{\odot k}\rangle_b=0\) for \(k=0,1,2\)
and \(\langle\mathbf q,\mathbf q\rangle_b=0\). The linear identities
compare the order-two branch with two leaves and append \(k\) leaves.
For the square, the order-five moments of
\((A\mathbf c)^{\odot2}\), \(A\mathbf c\odot\mathbf c^{\odot2}\), and
\(\mathbf c^{\odot4}\) are \(1/20,1/10,1/5\), respectively, giving
\(1/20-1/10+(1/4)(1/5)=0\).

Restrict to the physical stages with individually nonzero weights.
The weighted diagonal form there is nondegenerate, even if weights
are signed or repeated clocks occur. The span of
\(\mathbf 1,\mathbf c,\mathbf c^{\odot2}\) has Gram matrix
\[
H\coloneqq(1/(i+j+1))_{0\le i,j<3}
\]
by exact quadrature. Its leading principal minors are \(1,1/12,1/2160\);
the last is \(1/240-1/120+1/216=1/2160\) by first-row expansion.
Thus \(H\) is positive definite. Its orthogonal complement is
nondegenerate. With only four active rows that complement has
dimension one and its only isotropic vector is zero. Hence every
active row has \(q_i=0\) in that case.

## Why both initial defects are unavoidable over \(\mathbb Q\)

For a lower triangular method with common nonzero rational diagonal
\(\gamma\), the first physical row gives \(c_1=\gamma\) and
\(q_1=\gamma^2/2\ne0\). The second has \(a_{21}=c_2-\gamma\), so
\[
q_2=2\gamma c_2-\gamma^2-c_2^2/2.
\]
Its vanishing would require \(c_2=(2\pm\sqrt2)\gamma\), impossible over
the rationals with \(\gamma\ne0\). Both first weights must therefore
be zero whenever there are only four active rows. The
[published rational quadrature obstruction](order-five.md) requires
at least four distinct aggregate-weighted sites, hence at least four
active rows. Consequently a five-stage rational candidate cannot
have a zero weight.

## The nondegenerate five-dimensional boundary

When all five weights are nonzero, the ambient rational form is
nondegenerate in all five physical coordinates. The nondegenerate
three-dimensional Hilbert subspace above leaves a nondegenerate
two-dimensional complement. It contains the nonzero rational
isotropic vector \(\mathbf q\). Choose a rational \(\mathbf v\) in that
complement with \(a\coloneqq\langle\mathbf q,\mathbf v\rangle_b\ne0\),
possible by nondegeneracy. This pair has Gram determinant \(-a^2<0\)
and contributes one positive and one negative direction. The full
form has four positive directions and one negative direction;
as the physical Gram matrix is diagonal, exactly one weight is
negative.

Let \(D\) be the determinant of
\((\mathbf 1,\mathbf c,\mathbf c^{\odot2},\mathbf q,\mathbf v)\) in the
physical basis. It is nonzero since the Hilbert subspace and the
displayed complementary pair are nondegenerate. Comparison of Gram
determinants gives
\[
D^2\prod_i b_i=-a^2/2160,\qquad
-15\prod_i b_i=\left(\frac{a}{12D}\right)^2.
\]
This condition excludes compressing the six-stage splice simply by
shifting a positive-weight representative into the core. The two
equal-clock core/suffix pairs of the [six-stage witness](order-five-six-stage-splice.md)
also cannot be literally identified: the order-three chain value is
\(1\) at the first core row versus \(1/2\) at the suffix \(x=1\), and
\(-1\) at the second core row versus \(0\) at the suffix \(x=0\).
A different signed five-stage construction is not excluded.
