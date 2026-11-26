# Nonconsecutive lattice gaps: a saturation obstruction

## Result and scope

Use the already proved one-step reduced moment consequence of
literal order. For a finite tableau put \(c=A\mathbf1\),
\(H=\operatorname{diag}(c)A-A\operatorname{diag}(c)\), and
\[
 \mu(\delta)=\sum_{i,j:c_i-c_j=\delta} b_iH_{ij},\qquad
 G=\{\delta:\mu(\delta)\ne0\}.
\]
At order p,
\(\sum_\delta\mu(\delta)\delta^q=1/((q+2)(q+3))\) for
\(0\le q\le p-3\). These are the moments of \(x(1-x)\,dx\)
on [0,1]. Assume real coefficients and \(G\subset\lambda\mathbb Z\)
for some real \(\lambda\ne0\), and put \(g=|G|\).
The assumption holds whenever all stage clocks lie on an affine
lattice; their affine origin cancels. It also holds for any finite
set of rational gaps. The surviving labels may omit arbitrarily
many strides, the scale need not be rational a priori, and there
is no weight sign assumption.

**If \(g\ge2\), then \(p\le2g+1\).** The generic gap count only gives
\(p\le2g+2\). In particular at every even order \(p\ge6\) an affine
lattice needs at least \(p/2\) different net live gaps, one more
than the unstructured gap count. For all \(p\ge5\) the bound reads
\(g\ge\lceil(p-1)/2\rceil\). The cases \(g=0,1\) retain \(p\le2,4\).
This is a restriction on actual numerical net gaps, not on the
number of physical stages, the width of a consecutive level band,
or attainability by all the full rooted conditions.

## Saturated moments force rational splitting

Suppose \(p\ge2g+2\). The monic polynomial with the g gap labels
as roots is orthogonal to every polynomial of degree <g for
\(x(1-x)\,dx\): multiply by the test and use moments through
degree \(2g-1\). Let \(u=2x-1\) and let \(Q_g(u)\) be the resulting
monic degree-g orthogonal polynomial for \(1-u^2\) on [-1,1].
It is unique (positive Gram form), has rational coefficients,
and parity \(g\bmod2\). Therefore the mean of its raw x-roots is
1/2. Writing the gaps as \(\lambda k_i\) with distinct integer
\(k_i\), one gets
\(\lambda\sum_i k_i=g/2\), hence \(\lambda\in\mathbb Q\).
Thus all roots of \(Q_g\) would be rational. No separate
rationality hypothesis is needed for the real-lattice conclusion.

## Elementary 2-adic obstruction to full rational splitting

For every \(n\), the monic \(Q_n\) is an eigenpolynomial of
\(L=(1-u^2)\partial_u^2-4u\partial_u\) at eigenvalue \(-n(n+3)\).
Indeed \((1-u^2)Lf=((1-u^2)^2 f')'\), so L is self-adjoint and
preserves degrees, and leading coefficient plus orthogonality
gives the eigen-equation. Comparing coefficients in that
equation gives, for \(0\le j\le\lfloor n/2\rfloor\),
\[
 [u^{n-2j}]Q_n
  =(-1)^j\frac{n!}{(n-2j)!\,2^j j!\,
                 \prod_{\ell=1}^{j}(2n-2\ell+3)} .
\]
All these coefficients are 2-integral: the even factors in
\(n!/(n-2j)!\) are exactly
\(2^j j!\binom{\lfloor n/2\rfloor}{j}\). The remaining numerator
and denominator factors are odd. The coefficient at \(j=m\),
where \(m=\lfloor n/2\rfloor\), is a 2-adic unit; more generally
the reduction mod 2 is
\(u^{n\bmod2}(u+1)^{2m}\).

If \(Q_g\) split into rational linear factors, every rational
root would be 2-integral (otherwise the leading monomial has
strictly smaller valuation than every other term). Its nonzero
roots \(r\) must be 2-adic units, by the unit constant term after
factoring off the parity power of u. The roots come in m pairs
\(\{r_j,-r_j\}\). For a rational unit \(r=a/b\) with a,b odd,
\(r^2\equiv1\bmod8\), hence
\[
   v_2(Q_g(1))=\sum_{j=1}^m v_2(1-r_j^2)\ \ge\ 3m .
\]

On the other hand one can compute \(Q_g(1)\) without any outside
root theorem. Let
\[
 P_n(u)=\frac{1}{2^n n!}\,
          \partial_u^n (u^2-1)^n .
\]
Integration by parts gives ordinary Legendre orthogonality.
A further integration by parts shows that \(P_{g+1}'\) is
orthogonal for \(1-u^2\) in all degrees <g, since
\(\partial_u((1-u^2)f)\) has degree at most g for such a test f.
The leading coefficient of \(P_n\) is
\(2^{-n}\binom{2n}{n}\), while \(P_n'(1)=n(n+1)/2\), the latter
by expanding \((u^2-1)^n\) about u=1. Hence exactly
\[
 Q_g(1)=\frac{2^g(g+2)}{\binom{2g+2}{g+1}}
       =\frac{2^g(g+1)}{\binom{2g+2}{g}}>0 .
\]
When g is even, the second form gives \(v_2(Q_g(1))\le g=2m\).
When g is odd, the first form gives \(\le g-1=2m\) because
g+2 is odd and the central binomial coefficient is even.
For \(g\ge2\), this contradicts \(3m\). This proves the
no-splitting and lattice saturation results.

## Exact limits of a one-step reduced-moment argument

The stronger consecutive-ladder bound cannot be extended to
all omitted patterns using only these one-step moments. In
fact there are infinitely many rational **two-gap measures**
matching the entire degree-2 budget (the one-step budget
at order 5). Normalize the beta measure to mass 1, mean 1/2,
and variance 1/20. For any rational \(t\in(1/10,1/2)\), use
nodes \(1/2-t,\ 1/2+z\) with \(z=1/(20t)\), and weights
\(z/(t+z),\ t/(t+z)\), then divide the weights by 6 to restore
the original mass. The mean is 1/2 and variance \(tz=1/20\).
Both nodes are rational, lie in (0,1), and share a lattice.

For example, gaps \(1/4,7/10\) (primitive strides 5 and 14 on
scale 1/20) and masses \(2/27,5/54\) give exactly
\(1/6,1/12,1/20\) at powers 0,1,2. This is an exact reduced
counterexample to a universal \(p\le2g\) argument from the
one-step gap moments. It is **not** an RK order-five witness,
does not claim all two-sided or multi-step observables,
and does not prove the upper bound sharp at every g.
