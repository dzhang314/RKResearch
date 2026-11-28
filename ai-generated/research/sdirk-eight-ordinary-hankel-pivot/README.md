# Ordinary Hankel pivots are structural in the five-site boundary

The five-live-site ordinary moment reduction at strict ten-stage SDIRK order eight does not have a separate singular Cramer branch. This is a moment assertion, independent of strictness, of the residual interpolation, and of the signs of the output weights. It also applies on any other exactly supported ordinary measure with enough moments.

Let \(x_1,\ldots,x_m\) be the distinct live scalar clocks and \(\mathbf b\) their nonzero weights, over a field. Suppose \(k\) of the clocks \(s_1,\ldots,s_k\) are already known. Put \(P(T)=\prod_{j=1}^k(T-s_j)\), \(n=m-k\), and write \(x_a\) for the remaining \(n\) clocks. If
\[
I(T^d)=\sum_{i=1}^m b_i x_i^d
\]
holds through degree \(k+2n-2\), then the masked Hankel matrix
\[
H_{ij}=I(T^{i+j}P(T)),\quad 0\le i,j<n
\]
is exactly \(V^\mathsf T\operatorname{diag}(b_a P(x_a))V\), where \(V_{ai}=x_a^i\). Its determinant is
\[
 \det H=(\det V)^2\prod_{a=1}^n b_aP(x_a)\ne0 .
\]
No positivity or reality is used. Over any commutative ring the same determinant identity holds and the determinant is a unit if all the remaining weights and all differences of a remaining clock from another clock are units. Over an integral domain nonzero differences and weights suffice for nonvanishing; they need not give a unit.

If the moments also hold through degree \(k+2n-1\), the monic polynomial \(Q(T)=T^n+\sum_{j=0}^{n-1}q_jT^j\) on the unknown clocks satisfies
\[
 \sum_{j=0}^{n-1}H_{ij}q_j=-I(T^{i+n}P(T)).
\]
Indeed the corresponding weighted evaluation of \(T^iP Q\) vanishes at every live site. Thus \(\mathbf q\) is recovered uniquely by the ordinary Cramer system. The division-free Cramer identities and their unit-guarded uniqueness are both checked in Lean.

In the five-live-site order-eight boundary (\(m=5\)), masking any \(1\le k\le4\) already known clocks uses ordinary degrees at most \(k+2(5-k)-1=9-k\). **For \(k\ge2\)**, this is at most seven, so both the determinant and full recurrence are paid by the order-eight ordinary moments. With \(k=1\) the determinant already uses degree seven, but the final recurrence row requests degree eight; it is not supplied by ordinary order eight. These observations explain the \(\Delta\ne0\) guard in the live-eighth (three known clocks) and silent-eighth (two known clocks) graph charts. They do not assert that an extra nonlinear graph gate has a nonsingular Jacobian, or exclude a configuration that has fewer distinct live clocks.

The independent Mathlib module `RKCert.Research.SDIRKEightOrdinaryHankelPivot` records the abstract determinant factor, its field/nonzero and ring/unit variants, and the Cramer consequence under an explicit masked moment hypothesis. `proof-audit.lean` checks its standard axiom dependencies. Substitution of the specific order-eight ordinary moment functional is the mathematical step above; this is not a new global Runge–Kutta stage bound.

The [companion Gauss guard](../../lean/RKCert/Research/SDIRKEightOrdinaryGaussGuard.lean)
proves that a five-site ordinary order-eight quadrature over an integral
domain, with distinct clocks and nonzero weights, cannot contain a root
of the fourth shifted Legendre polynomial. Its proof deletes any
hypothesized zero coordinate from the Vandermonde null vector, then
uses the degree-four root bound to rule out the zero vector. It
checks the degree-seven moment cancellations without denominators in
the statement. The accompanying Lean/Mathlib 4.36.0 audit uses standard
axioms only. The remaining SDIRK chronology deductions are separate.
