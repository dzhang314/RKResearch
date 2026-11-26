# Actual composability couples H and H² beyond their gap totals

Let \(c=A\mathbf1\), \(C=\operatorname{diag}(c)\), and \(H=CA-AC\).
All gaps may live on a single affine clock lattice; the mathematical
identities do not need consecutivity, distinct clock copies, or a
weight sign assumption. Write \(e=c_i-c_j\) for the outgoing gap
of the two-edge segment \(k\to j\to i\), and \(a=c_j-c_k\) for
its incoming gap. For each **actual** intermediate stage j set
\[
 U_j(a)=\sum_{k:c_j-c_k=a}H_{jk},\qquad
 V_j(e)=\sum_{i:c_i-c_j=e}b_iH_{ij}.
\]
Define the ordered-pair mass \(\Theta(a,e)=\sum_jU_j(a)V_j(e)\).
The earlier one-step and two-step reduced gap measures satisfy
\[
 \mu_1(e)=\sum_jV_j(e),\qquad
 \mu_2(d)=\sum_{a+e=d}\Theta(a,e).
\]
These are exact groupings of actual products \(b_iH_{ij}H_{jk}\).
Replacing them by an arbitrary convolution or by formal addition
of two marginal supports discards the shared stage j.

## A direct obstruction using just the two reduced measures

Suppose every actual predecessor j of a live H receiver has
the same inbound gap profile \(U_j=\nu\). It suffices that this
holds for j with nonzero \(V_j\); the literal edge premise is
simpler to recognize. Then actual composability yields
\(\Theta(a,e)=\nu(a)\mu_1(e)\) and \(\mu_2=\nu*\mu_1\).
This holds for a common repeated-block stencil; identical support
alone or proportional but unequal profiles does not imply it.

At \(p\ge7\) the two reduced moment identities give:
\[
\begin{array}{c|ccc}
 &\text{mass}&\text{normalized mean}&\text{normalized variance}\\ \hline
 \mu_1 &1/6&1/2&1/20\\
 \mu_2 &1/120&2/3&2/63 .
\end{array}
\]
The normalized variance here is an algebraic moment difference,
even for a signed measure. From convolution, \(\nu\) has
mass \(1/20\), normalized mean \(1/6\), and
\[
       \operatorname{Var}(\nu)=2/63-1/20=-23/1260 .
\]
The usual additivity follows by expanding the second power;
no positivity of \(\mu_1\) or of the b entries is involved.
Thus **no nonnegative common inbound stencil** can attain
order 7. The condition is satisfied, for example, by a
uniform inbound gap profile whose actual incoming H entries
are nonnegative. In the common-profile class at least one
net negative inbound gap mass is necessary at order 7.
Already at order 6 the profile mean is forced to \(1/6\);
if its normalized shape equals that of \(\mu_1\) (stationary
identical normalized stencils), the mean would be \(1/2\).
This is a cross-order obstruction using only the original
two one-dimensional paid measures and genuine composability,
not a stage count or a stricter one-step estimate.

## The missing middle-clock information

With one allowed probe at the intervening stage and more as
paid, the full literal order implies
\[
 \sum_{a,e}\Theta(a,e)a^r e^s
   =\frac{(r+1)!(s+1)!}{(r+s+5)!},
 \qquad r+s+5\le p. \tag{*}
\]
To derive this, the word
\(\mathbf b \cdot (C^\ell H C^m H C^q\mathbf 1)\) expands into literal
equal-size trees of order \(5+\ell+m+q\). Under the established
exact polynomial model \(C\mapsto M_x\), \(H\mapsto J^2\),
its scalar is the iterated integration on
\(0\le x\le y\le z\le1\) with the factors \((y-x)(z-y)\)
and the corresponding powers of x,y,z. Binomial expansion
of \((y-x)^r(z-y)^s\) uses only the same paid total degree.
Putting \(a=y-x,\ e=z-y\) leaves
\[
 \int_{a,e\ge0,\ a+e\le1} a^{r+1}e^{s+1}(1-a-e)\,da\,de.
\]
Integrating first in e gives
\(a^{r+1}(1-a)^{s+3}/((s+2)(s+3))\), and the integer beta
integral gives (*). This is also a rational polynomial
calculation by formal integration over the ordered simplex;
it needs no probabilistic model for actual RK weights.
Every denominator is paid by literal tree order.

**Even constant mass fails already at order 6.** If the
inbound H row sums \(\sum_aU_j(a)\) are all the same \(\sigma\)
on actual live predecessors, then the outgoing second-jump
marginal \(\Theta_{\rm out}(e)=\sum_a\Theta(a,e)\) equals
\(\sigma\mu_1(e)\). At order 5 its mass forces
\(\sigma=1/20\); at order 6 its first moment by (*) is \(1/360\),
whereas \(\sigma\mu_1\) has first moment \(1/240\).
This stronger obstruction allows different and signed
inbound profiles provided their masses are constant.
It uses the outgoing-jump moment, which the reduced total
gap of H² does not itself record.

Optional calibration: if for each literal live incoming edge
\(j\to i\) the middle row sum is \(P(c_i-c_j)\) for one polynomial
P of degree at most d, then
\(\Theta_{\rm out}(e)=P(e)\mu_1(e)\).
The ideal outgoing marginal is \(x(1-x)^3/6\), versus
\(x(1-x)\) for \(\mu_1\). Let \(t=\max(d,2)\).
If \(p\ge\max(t+5,t+d+3)\), both word budgets pay tests
\(x^q\) for \(0\le q\le t\). Their equality gives
orthogonality of \(P-(1-x)^2/6\) to degree \(\le t\) for
\(x(1-x)\). Testing by the difference itself forces
\(P=(1-x)^2/6\). This also rules out a shared affine dependence
at \(p\ge7\), not just a constant mass.

## Two more topology consequences of (*)

* At \(p\ge2r+5\) the spaces spanned by actual incoming profiles
  \(U_j\) and outgoing live profiles \(V_j\) each have dimension
  at least r+1. Indeed the (r+1)-square joint moment matrix
  \(M_{ij}=(i+1)!(j+1)!/(i+j+5)!\) factors through these profiles.
  Divide away the numerator row/column factors and multiply
  row i by \((i+r+5)!\). Column j is then a monic polynomial
  in i of degree \(r-j\), namely
  \(\prod_{\ell=j+1}^r(i+5+\ell)\). Its evaluation determinant
  is Vandermonde up to sign. So one profile direction, even
  with arbitrary signed proportionality, precludes order 7.
  More generally at most d independent profiles implies
  \(p\le2d+4\), independently of repetitions or stage count.
* At \(p\ge2d+5\) the support of surviving ordered gap pairs
  cannot be contained in the zero set of a nonzero polynomial
  of degree d. Its square would vanish on every actual surviving
  pair, but (*) gives the strictly positive integral of that
  square against \(ae(1-a-e)\) on the open triangle. A union
  of d affine lines gives the same obstruction by their product.
  In particular, **no same-stride-only continuation** at order
  7: at that order the exact paid sum of \((a-e)^2\) is
  \(2/840-2/1260=1/1260\), not zero. Equal successive strides
  in every legal two-step path would give zero even with
  arbitrarily many different individual strides.

These statements refer to actual shared-stage composition and
actual weighted sums, not a coalesced substitute. The pure
variance obstruction uses only the two original reduced
measures; the others explicitly pay the missing middle-clock
information. No claim about an unstructured stage floor.
