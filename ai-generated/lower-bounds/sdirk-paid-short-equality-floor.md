# Order at least nine needs more stages than order at a common diagonal

**Theorem.** Let \(R\) be a nonzero commutative ring with identity.
If a triangular RK tableau over \(R\) has a common diagonal and
satisfies the denominator-cleared rooted equations through \(p\ge9\),
then \(s\ge p+1\).

Pass to any maximal residue field; its characteristic is zero or a
prime above \(p\) because the paid bushes make \(1,\ldots,p\) units.
The [paid tall recurrence](../research/strict-sdirk-dependency-depth/CHARACTERISTIC-TRANSFER.md)
excludes \(s\le p-2\) for nonzero diagonal, and the
[marked full chain](../research/strict-sdirk-dependency-depth/DECORATED-SATURATION.md)
excludes \(s=p-1\). At \(s=p\), the
[four-clock vanishing test](../research/strict-sdirk-dependency-depth/FOUR-CLOCK-VANISHING.md)
excludes a zero longest strict read, including by truncation when
the last output weight is zero. Below is the remaining case of a
nonzero longest strict read. For zero diagonal, the paid explicit
rectangle excludes \(s=p\) and the ordinary tall read excludes \(s<p\).

The bound applies to common diagonals only. It does not improve the
larger tabulated stage lower bounds already known through order 20.

Zero diagonal is covered by the paid explicit equality rectangle.
Hence below \(\gamma\ne0\). Write \(B=A-\gamma I\),
\(\mathbf c=A\mathbf 1\), and
\(\lambda_j=\mathbf b\cdot(B^j\mathbf 1)\) for \(j+1\le p\).
Use the bounded formal clock model \(B\mapsto T=J-\gamma I\),
\(C=\operatorname{diag}(\mathbf c)\mapsto X\), with formal output
\(\ell\). An expression with \(d\) strict hops and total clock
degree \(h\) is paid at order \(d+h+1\).

## 1. Arbitrary boundary roots: a short paid product test

Suppose \(L=\lambda_{s-1}\ne0\). Then all actual adjacent strict
entries and \(b_s\) are nonzero. For \(j+k\le s-1\), choose the
actual boundary polynomials
\[
 P_j(z)\coloneqq\prod_{a=1}^{j}(z-c_a),\qquad
 Q_k(z)\coloneqq\prod_{a=1}^{k}(c_{s+1-a}-z).
\]
On paths with \(j+k\) holes, mark the first retained clock by
\(P_j\) and the last by \(Q_k\). Fewer than \(j\) leading holes
kills the first mark; fewer than \(k\) trailing holes kills the
second. Thus only the single allocation of \(j\) leading and \(k\)
trailing holes can contribute. The prospective surviving values
\(P_j(c_{j+1})\) and \(Q_k(c_{s-k})\) need not be known or nonzero.
The leading and trailing weight ratios concern disjoint physical
edge blocks, even if the remaining endpoints coincide. The joint
marked output is the product of the two separately calibrated
single-end outputs divided by \(L\). In particular it keeps the
surviving mark values in *both* the single-end and combined
outputs; it does not divide by either value. Repeated clocks give
no problem.

Define \(U_j,V_k\) by the ordinary polynomial actions
\[
 P_j(X)1=j!T^jU_j(\gamma/T)1,\qquad
 Q_k(1-X)1=k!T^kV_k(\gamma/T)1.
\]
The expressions are read after clearing powers of \(T\), not by
inverting the operator. On the formal degree window, reflection
in \(x\mapsto1-x\) conjugates \(J\) to its adjoint under
\(\ell(fg)\). The adjunction on monomials uses the identity
\[
 \frac{1}{(u+1)(u+v+2)}
 =\frac{1}{v+1}
     \left(\frac{1}{u+1}-\frac{1}{u+v+2}\right),
                     \qquad u+v+2\le s.
\]
Reflection of the polynomial primitive has the same derivative
and endpoint value as the adjoint primitive. Uniqueness uses
only unit casts of positive indices in the degree window.
Moving the trailing polynomial of \(T^\ast\) across the pairing
therefore gives the combined output
\(j!k!L\,\mu(U_jV_k)\), where
\(\mu(y^a)=\gamma^a\lambda_{s-1-a}/L\).
The single-end expressions give \(j!L\mu(U_j)\) and
\(k!L\mu(V_k)\). All have rooted order at most \(s\).
Consequently
\[
                  \mu(U_jV_k)=\mu(U_j)\mu(V_k).
\]
The mask uses the first \(j\) and last \(k\) *deficit clocks*,
not \(j+1\) or \(k+1\) arithmetic clocks. This distinction is
also what allows nonarithmetic roots on the shorter side.

## 2. Cyclic equality, including exceptional slope

The nondegenerate rectangle gives global arithmetic clocks.
In the degenerate chart without a split, the arithmetic
prefix through \(s-2\) suffices. These have at least seven
clocks and are excluded by the paid local obstruction.
Otherwise the two endpoint runs have a common nonzero
step \(\delta\) and lengths summing to \(s-2\ge7\).
The first clock is \(\gamma\), and the last is \(1-\gamma\).
The latter follows algebraically from the affine tail:
with \(n=s-2\), \(z=\gamma^{-1}-2\), \(m_j=\mu(y^j)\),
\(k_0=1+2m_1+m_2\), \(l_0=m_1+2m_2+m_3\), the first
reverse tall rows give \(nk_0=zm_1-2\) and
\((n-1)l_0=zm_2-2m_1\). Thus
\[
 (n-1)(m_1 k_0-l_0)+m_1 k_0=-z(m_2-m_1^2).
\]
Here \(m_1k_0-l_0=\gamma E/L^2\),
\(m_1k_0=\gamma H/L^2\),
\(m_2-m_1^2=\gamma^2D/L^2\) in the rectangle, and
\(\delta=-E/D\). Substitution in
\(c_s-\gamma=(s-3)\delta-H/D\) gives the claim.
In the reflected trailing coordinates the arithmetic deficit
clocks therefore start at \(\gamma\) with step \(\delta\),
exactly as at the leading end.

As before put \(t=\delta/\gamma\),
\({\cal D}=m_2-m_1^2\ne0\), and \(g=F_1-\mu(F_1)\).
The degenerate rectangle gives \(\mu(gy^k)=0\) for
\(k=0,1,2\). For an arithmetic end the polynomials of
degrees \(1,2,3\) defined in Section 1 are
\[
 H_1=1,\qquad H_2=(1+F_1)/2,\qquad
 H_3=(1+3F_1+2F_2)/6.
\]
Only the relevant deficit clocks must be arithmetic.
If \(t\ne2/3\) and the shorter run has at least two clocks,
pair \(H_2\) there with \(H_3\) on the longer run (which has
at least three). Multiplicativity gives \(\mu(gH_3)=0\);
the cubic coefficient \((1-3t/2)/3\ne0\) yields
\(\mu(gy^3)=0\). If the shorter run has exactly one clock,
the longer has at least six; the existing internal
\(F_1F_2\) calibration gives the same missing moment.

Now let \(t=2/3\). There is a good end with at least three
arithmetic deficit clocks. In this case \(H_3\) has degree
two and
\[
 H_3-\mu(H_3)=\alpha g+\beta (y-m_1),\qquad
                          \beta=2/81\ne0.
\]
Indeed \(F_2-(13/9)F_1=-4/9+(2/27)y\). The opposite end
has first deficit root \(\gamma\), using reflected
coordinates if needed. If its actual second deficit
root is \(\gamma+\eta\), its quadratic boundary polynomial
in the reverse model is
\[
                         H_2+c y,\qquad c=(\delta-\eta)/(2\gamma).
\]
Pair this with the good \(H_3\). The known annihilations
make its covariance with \(H_3\) equal to
\(c\beta{\cal D}\), so \(c=0\). This forces the actual
second deficit root onto the arithmetic continuation.

With that second root fixed, if the actual third is
\(\gamma+\zeta\), its cubic reverse polynomial is
\[
                  H_3+d yH_2,\qquad d=(2\delta-\zeta)/(3\gamma).
\]
These two correction formulas follow by subtracting the
standard boundary products in \(X\), since the differences
are a constant times the preceding standard product.
Pair the actual cubic with the good \(H_2\); its covariance
is \(d\,\mu(gy^3)/4\). If \(d\ne0\) this supplies the missing
fourth annihilation. If \(d=0\), both cubic probes are \(H_3\)
and their covariance is \(\beta^2{\cal D}\ne0\), itself
a contradiction. In particular this handles even a short
opposite end of one or two clocks. No arithmetic extension
was assumed for its actual second or third root before testing.

In every branch where the fourth annihilation is obtained,
the first four reverse tall rows rule out the resulting
fixed quadratic recurrence, as in the [arithmetic-gap proof](../research/strict-sdirk-dependency-depth/PAID-ARITHMETIC-GAP-EXCLUSION.md).
