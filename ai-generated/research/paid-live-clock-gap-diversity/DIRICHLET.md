# Multihop paid Dirichlet identity and unit Gram

## Actual joint gaps and their exact payment

Let R be a nontrivial commutative ring and a finite tableau have
literal rooted order p. Put \(\mathbf c=A\mathbf 1\),
\(C=\operatorname{diag}(\mathbf c)\), and \(H=CA-AC\).
For an actual ordered h-edge walk \(i_0,\ldots,i_h\), write
\(\delta_j=c_{i_j}-c_{i_{j-1}}\). Let \(\Theta_h\) be the finite
net measure on **ordered** tuples \(\boldsymbol\delta\in R^h\),
obtained by summing \(b_{i_h}\prod_{j=1}^h H_{i_j i_{j-1}}\)
over every walk with the same tuple. The shared indices are
actual stages; no independent concatenation of marginals is used.

For \(\alpha\in\mathbb N^h\) let
\(M_\alpha=\sum_{\boldsymbol\delta}\Theta_h(\boldsymbol\delta)
\boldsymbol\delta^\alpha\). If \(N=2h+|\alpha|+1\le p\), then
\[
                   (N!:R)M_\alpha
                     =\prod_{j=1}^h(\alpha_j+1)!:R.       \tag{1}
\]
The measure is not normalized: \(M_0=1/(2h+1)!\).

Here is a finite tree justification. Expand each gap power
binomially. Every term is a scalar word
\(\mathbf b\cdot(C^{k_h}H C^{k_{h-1}}\cdots H C^{k_0}\mathbf 1)\),
with \(\sum k_i=|\alpha|\). Expand H into \(CA-AC\).
A adds a unary branch; C adds a leaf at the current root
because \(\mathbf c=A\mathbf 1\). Thus all terms are evaluated by actual
literal rooted trees of size N. For a size-N tree t write
\(\gamma(t)=NF(t)\), where \(F\) is its forest factorial.
Then \(F(t)\mid(N-1)!\): for a join of sizes u,v its forest
factorial is \(F_{\rm base}\,vF_{\rm branch}\), which divides
\((u-1)!v!\), itself dividing \((u+v-1)!\). Consequently
multiplying each exact tree output by N! gives the integer
\(N!/\gamma(t)\) cast to R, before summing.

Compute those cleared integers in the rational polynomial
model \(A\mapsto J,\ C\mapsto M_x\), where J is the formal
antiderivative with zero constant. The raw ideal polynomial
of t is \(x^{N-1}/F(t)\), by the unary and leaf attachments.
The commutator \(M_xJ-JM_x=J^2\) has kernel \(y-x\) on a
single Volterra hop \(x\le y\) (equivalently test monomials).
The word trace over \(0\le x_0\le\cdots\le x_h\le1\) thus
contributes the gap factors \(\prod_j(x_j-x_{j-1})\).
After projecting to the gap tuple, the initial location \(x_0\)
runs over an interval of length \(1-\sum\delta_j\). The formal
moments are therefore
\[
 \int_{\substack{\delta_j\ge0\\ \sum_j\delta_j\le1}}
     \Bigl(1-\sum_j\delta_j\Bigr)\prod_j\delta_j^{\alpha_j+1}
      \,d\boldsymbol\delta
       =\frac{\prod_j(\alpha_j+1)!}{(2h+|\alpha|+1)!}.
\]
The equality is iterated integer beta integration (polynomial
antiderivatives suffice). All h gap coordinates and the
leftover coordinate have parameter 2. Comparing the cleared
integers gives (1) in R; no integration or map from \(\mathbb Q\)
is needed inside that ring. The paid bush of size k gives that
each \((k:R)\), \(1\le k\le p\), is a unit. Inverses below always
mean inverses of such units or their products.

## A general Dirichlet unit-Gram lemma

For positive integer parameters \(d_0,d_1,\ldots,d_h\) put
\(D=\sum_{i=0}^h d_i\). The standard unnormalized functional on
the h-simplex has formal moments
\[
 \Lambda(x^\alpha)=
 \frac{(d_0-1)!\,\prod_{i=1}^h(d_i+\alpha_i-1)!}
      {(D+|\alpha|-1)!}.
\]
If \(D+2r-1\le p\) and the positive integers through p are
units in R, its Gram matrix on the monomial basis
\(\{x^\alpha:|\alpha|\le r\}\) has unit determinant.
The proof gives an explicit unitriangular orthogonal basis.

First, for the beta weight \(x^A(1-x)^B\), \(A,B\ge0\), the
monic degree-n polynomial J has norm
\[
 \mathcal N(n;A,B)=
   \frac{n!(n+A+B)!(n+A)!(n+B)!}
        {(2n+A+B)!(2n+A+B+1)!}.                         \tag{2}
\]
Indeed use the Rodrigues polynomial
\([x^A(1-x)^B]^{-1}\partial_x^n(x^{n+A}(1-x)^{n+B})\).
Leibniz shows it is a polynomial with integer coefficients;
its leading coefficient is
\((-1)^n(2n+A+B)!/(n+A+B)!\). Divide by that scalar to
obtain J. Integration by parts n times proves orthogonality.
The norm equals its pairing with \(x^n\); after that same
integration by parts it is the beta integral of
\(x^{n+A}(1-x)^{n+B}\) times n! divided by the absolute leading
coefficient, giving (2).

Now split off the first coordinate \(s=x_1\), writing
\(x_{2:h}=(1-s)y\). If \(D'=D-d_1\), the weight and Jacobian
split into \(s^{d_1-1}(1-s)^{D'-1}\) times the tail Dirichlet
weight for \(d_0,d_2,\ldots,d_h\). Inductively use its tail
orthogonal polynomial \(Q_\beta(y)\) of degree \(t=|\beta|\),
leading monomial \(y^\beta\) with coefficient one. For a
multi-index \(\alpha=(n,\beta)\), define
\[
 Q_\alpha(x)=
  (1-x_1)^t Q_\beta\bigl(x_{2:h}/(1-x_1)\bigr)
       J_n^{(d_1-1,\ D'-1+2t)}(x_1).
\]
Homogenization denotes a polynomial: each tail monomial
\(y^\gamma\) is replaced by
\(x_{2:h}^\gamma(1-x_1)^{t-|\gamma|}\).
Cross-products with unequal tail indices vanish by tail
orthogonality; for equal indices the remaining s factor is
the displayed beta weight with the extra \(2t\). Hence the
norm is the tail norm times (2).

Order monomials by the lexicographic tuple of suffix degrees
\[
 (|\alpha|,\ |\alpha_{2:h}|,\ |\alpha_{3:h}|,\ldots,\alpha_h).
\]
The constructed \(Q_\alpha\) has leading monomial \(x^\alpha\)
of coefficient one: a lower tail degree stays lower in the
suffix comparison even after homogenization, and a tail
monomial of the same degree that is lower in the tail order
also stays lower. Lower powers from the monic univariate factor
have smaller total degree. Consequently the whole basis
change on total degree ≤r is **unitriangular** with determinant
one, not just an abstract invertible real basis change.

For an explicit product norm, in each split i let
\(t_i=\sum_{j>i}\alpha_j\),
\(D_{i+1}=d_0+\sum_{j>i}d_j\),
\(A_i=d_i-1\), \(B_i=D_{i+1}-1+2t_i\).
Then the diagonal norm is
\(\prod_{i=1}^h\mathcal N(\alpha_i;A_i,B_i)\);
the Gram determinant is the product of these norms over
\(|\alpha|\le r\). The largest factorial argument at split i is
\[
 2\alpha_i+A_i+B_i+1
   =2\sum_{j\ge i}\alpha_j+d_0+\sum_{j\ge i}d_j-1
   \le D+2r-1.
\]
For the H-hop task \(d_0=\cdots=d_h=2\), this is at most
**\(2h+2r+1\)**, exactly the paid bound. All smaller factorial
arguments in the Rodrigues leading coefficient, the basis
coefficients, the moments, and (2) are therefore paid.
The rational orthogonality identities specialize through
\(\mathbb Z[1/p!]\to R\); all their coefficients and values lie
in that localization. There is no real-positivity assumption
in the unit-Gram conclusion.

## Joint support, not a stage census

Under \(2h+2r+1\le p\), let S be the finite support where the
**signed net** mass \(\Theta_h\) is nonzero. Evaluation E on
S (rows tuples, columns the monomials of degree ≤r) satisfies
\[
 G=E^T\operatorname{diag}(\Theta_h|_S)E.
\]
The unit Gram makes E split injective, with left inverse
\(G^{-1}E^T\operatorname{diag}(\Theta_h|_S)\). In particular
no nonzero degree-≤r polynomial vanishes on S, and
\[
                   |S|\ge\binom{h+r}{h}.
\]
If there were fewer tuples, the factorization would force
zero determinant by multilinearity, including over rings
with zero divisors. Every surviving tuple has at least one
nonzero actual walk term, but a tuple may aggregate many
walks and masses may cancel. This counts neither individual
hop labels nor disjoint/independent branches or stages.
Different words can share almost all their physical stages.
