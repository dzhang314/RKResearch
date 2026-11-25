# Exact 2-adic support gaps for centered symmetric quadrature through order 20

**Result.** For uniform quadrature symmetric under reflection about the midpoint, the elementary square-moment method gives the exact support floor over \(\mathbb Q_2\) through order 20, in each parity. Rational supports obey the same lower bounds, but the upper examples over \(\mathbb Q_2\) are not upper bounds over \(\mathbb Q\). In particular, the actual 17-site symmetric order-20 endpoint is possible over \(\mathbb Q_2\) with all sites distinct and active, without any lower-order nesting assumption. Both allowable dyadic strata are realized. A genuine real quadratic example also has the same rational weights and all real sites in the integration interval, while its last pair is provably not rational.

## 1. Both centered support parities

In centered \(Y=2X-1\) coordinates use the formal uniform probability moments
\[
   L(Y^{2j})=\frac1{2j+1},\qquad L(Y^{2j+1})=0 .
\]
Say \(p\) moments are paid if all degrees \(0,\ldots,p-1\) are exact. A centered symmetric support consists of \(r\) pairs \(\pm a_i\) and optionally the center. Put \(e=0\) or \(1\) for the presence of the center and \(m=2r+e\). The \(a_i\) are nonzero with distinct squares, and the nodal polynomial is \(P(Y)=Y^e H(Y^2)\), where \(H(T)=\prod_i(T-a_i^2)\). For support with \(m\le p\), the weights are forced by Vandermonde; the reflection of these weights must agree with them. Therefore a paid odd order \(p\) automatically pays \(p+1\) (the monomial of degree \(p\) is odd). This can also be read directly if the weights were assumed symmetric.

Replace the requested order by \(P_+=2N=2\lceil p/2\rceil\). Polynomial division by the nodal polynomial says that the first \(P_+\) moments are exact at the interpolatory weights if and only if \(L(Y^jP)=0\) for \(0\le j<P_+-m\). The odd terms vanish automatically, and the remaining equations are
\[
 M_\alpha(T^jH)=0\quad(0\le j<t),\qquad
 \alpha=1+2e,\quad M_\alpha(T^j)=\frac1{2j+\alpha},\quad t=N-r-e.
\]
For exact order \(P_+\), the next omitted row \(M_\alpha(T^tH)\) must be nonzero. Claims about sparse supports below assume centered reflection \(X\mapsto1-X\), not merely an unrelated reflection symmetry of the unweighted node set about another center. If both nodes and weights are symmetric about another center, the first moment already fixes that center to be the midpoint.

## 2. Reusable dyadic test and the small-order cutoff

In \(\mathbb Q_2\) set \(Z=T-1\). Multiply each factor with \(v_2(a_i)<0\) by \(-a_i^{-2}\), so the normalized product has three types of factors:
\[
 T-\eta\quad(\eta\in4\mathbb Z_2),\qquad
 Z-\epsilon\quad(\epsilon\in8\mathbb Z_2),\qquad
 1-\theta T\quad(\theta\in4\mathbb Z_2).
\]
The middle type occurs at the \(b\) magnitudes that are 2-adic units. Let \(c\) be the number of first-type factors. The unperturbed product is \(T^c Z^b\). Scaling does not change vanishing or ratios of moments.

For all nonnegative \(j,c,d\), and any positive odd \(\alpha\), the finite-difference identity gives
\[
 M_\alpha(T^{j+c}Z^d)=\frac{(-1)^d2^d d!}
       {\prod_{\ell=0}^{d}(\alpha+2j+2c+2\ell)} .
\]
This follows from the defining moment and induction: subtract the expression at \(j\) from that at \(j+1\) to add one \(Z\). Its valuation is \(v_d=d+v_2(d!)\). In \(M_\alpha(T^jZ^\ell H)\) write \(d=b+\ell\). A term using \(h\ge1\) unit-factor corrections has valuation at least \(3h+v_{d-h}\); any correction of either other type adds at least two, and changes only the \(T\)-power. This is a general one-line criterion: when \(2h>v_2(d!/(d-h)!)\) for all \(1\le h\le d\), the unperturbed term has a unique least valuation and the moment cannot vanish. With \(d\le9\) the exact comparisons are
\[
\begin{array}{c|rrrrrrrrrr}
d&0&1&2&3&4&5&6&7&8&9\\\hline
v_d&0&1&3&4&7&8&10&11&15&16\\
\min_{h\ge1}(3h+v_{d-h})&\infty&3&4&6&7&10&11&13&14&17
\end{array}
\]
The rows in \(T\)-powers are equivalent to the first \(t\) rows in \(Z\)-powers. For order at most 20, every needed exponent \(d=b+\ell\) satisfies \(d\le r+t-1=N-e-1\le9\). Thus every paid row requires \(d\in\{4,8\}\), and **two consecutive reduced rows are impossible**. For one paid row \(b\) must equal 4 or 8, in particular \(r\ge4\). For a one-row rule already paid, the next row \(M_\alpha(TH)=M_\alpha(ZH)\) cannot vanish, since \(b+1\) is 5 or 9. This last exactness statement also applies when the requested \(P_+\) happens to be 20.

## 3. The local floors are sharp

If \(t=0\), take rational magnitudes small, positive and distinct in the real topology. The interpolatory rule pays the required order. Every weight is nonzero: writing \(H_i=H/(T-a_i^2)\), the weight at either member of the pair is
\[
  \frac{M_1(H_i)}{2H'(a_i^2)}\quad(e=0),\qquad
  \frac{M_3(H_i)}{2a_i^2H'(a_i^2)}\quad(e=1);
\]
the center weight when present is \(M_1(H)/H(0)\). These formulas follow by integrating the Lagrange polynomial for its site. The numerators tend to nonzero monomial moments as all magnitudes tend to zero, and the denominators are nonzero off collisions. This constructs genuine rational, hence also \(\mathbb Q_2\), rules at the ordinary interpolation floor.

For \(t=1\) and \(r\ge4\), a one-row solution exists over \(\mathbb Q_2\), in either parity. More precisely choose \(b=4\), or \(b=8\) whenever \(r\ge8\). Fix \(r-1\) distinct nonzero rational magnitudes with \(b-1\) unit squares and \(r-b\) nonunits. Require the unit squares to be \(1\bmod16\) if \(b=4\), or \(1\bmod32\) if \(b=8\). Let \(K\) be their square product polynomial. The only remaining square value is
\[
       s=\frac{M_\alpha(TK)}{M_\alpha(K)}
        =1+\frac{M_\alpha(ZK)}{M_\alpha(K)} .
\]
In the two cases the stronger congruence makes the unperturbed moment once again strictly dominant, so
\[
 (v_2(M_\alpha(K)),v_2(M_\alpha(ZK)))=
       (4,7)\quad\text{or}\quad(11,15)
\]
in the normalized product. Therefore \(s\equiv9\bmod16\) or \(s\equiv17\bmod32\), respectively. These are units congruent to \(1\bmod8\), hence squares in \(\mathbb Q_2\) by Hensel's lemma. They differ from all the previous unit squares by the same congruences, and from the other squares by valuation. The new root pair thus gives a distinct support; its nodal equation vanishes exactly by construction. More generally, by prescribing the other unit squares sufficiently close to 1, the valuation of \(s-1\) is \(v_b-v_{b-1}=1+v_2(b)\), which gives a reusable one-row local construction whenever \(4\mid b\).

Every site of a distinct one-row support through order 20 is active. Indeed reflection forces equality of the pair weights; deleting any zero-weight pair (or deleting a zero-weight center if present) would increase \(t\) from one to two for the same paid order, which is impossible. The next omitted row is nonzero by Section 2. These statements hold over \(\mathbb Q_2\) independently of any sign convention.

Consequently the following are the **sharp minima over \(\mathbb Q_2\)** and lower bounds over \(\mathbb Q\) among centered symmetric supports. The table includes the two parities even where the unrestricted minimum would choose only one.
\[
\begin{array}{c|ccc}
P_+&\text{no center}&\text{center present}&\text{either parity}\\\hline
2,4,6,8&P_+&P_+-1&P_+-1\\
10&8&9&8\\
12,14,16,18,20&P_+-2&P_+-3&P_+-3
\end{array}
\]
For example at requested order 19 a 16-site centered symmetric rational rule is impossible, because it would automatically pay 20; a possibly nonsymmetric 16-site order-19 rule is not excluded. The table does not assert rational attainability in any one-row case.

## 4. Actual order 20 on seventeen sites: exact scope

Here \(r=8,e=1,\alpha=3\). Any rational solution must have either four or eight 2-adic unit magnitudes. There is a further exact residue gate in each case. Write \(q_i=(a_i^2-1)/8\) on the unit magnitudes and \(S=\sum_i q_i\). For \(b=4\), the only terms able to contribute to \(M_3(H)/2^7\bmod2\) are the unperturbed term and the first unit corrections; their sum is \(1+S\bmod2\), so \(S\equiv1\bmod2\). For \(b=8\), the unperturbed term contributes \(2\bmod4\) after division by \(2^{14}\); the first corrections contribute \(315S/D\bmod4=3S\bmod4\), where \(D\) is a product of eight consecutive odd numbers in steps of two and is \(1\bmod4\). All higher corrections have valuation at least 16. Hence \(S\equiv2\bmod4\). In terms of the sums of the unit squares, these are
\[
          \sum_{\mathrm{unit}\ i}a_i^2\equiv12\bmod16\ (b=4),\qquad
          \sum_{\mathrm{unit}\ i}a_i^2\equiv24\bmod32\ (b=8).
\]
The construction in Section 3 realizes both strata over \(\mathbb Q_2\) directly at order 20, without a nested order-16 or order-18 seed.

The same rational squared-node polynomial can also yield real interval sites, with rational weights and a provably nonrational last pair. To see this without a candidate scan, choose the fixed magnitudes in Section 3 as \(19/(115+608k)\) for the units and \(38/(115+608k)\) for the nonunits, using distinct sufficiently large positive integers \(k\) in each class. The denominators are \(19\bmod32\) and \(1\bmod19\). Thus the units are \(1\bmod32\); the nonunits have valuation one at two; and all fixed magnitudes vanish modulo 19. As these magnitudes approach zero over the reals, \(K\) tends to \(T^7\), and the forced \(s\) tends to \(17/19\). Choose \(k\) large enough that \(s\) lies strictly in \((0,1)\) and its real roots do not collide with any fixed site. This gives all real centered sites in \((-1,1)\), hence all physical sites in \((0,1)\) after the affine map. At the same time,
\[
            M_3(K)\equiv1/17\bmod19,\qquad
            M_3(TK)=1/19+\text{19-integral terms}.
\]
Therefore \(v_{19}(s)=-1\), so \(s\) is not a square over \(\mathbb Q\) or even over \(\mathbb Q_{19}\). Only its last reflected pair needs the real quadratic field \(\mathbb Q(\sqrt s)\). All weights are rational by the pair and center formulas above, which depend only on the squared nodes. They are nonzero over that field because the same rational formulas have already given active weights over \(\mathbb Q_2\). Exact order 20 transfers by the same nonzero rational defect.

This proves simultaneous real and 2-adic admissibility at the actual width, not a rational witness and not admissibility at every other prime for this example. No purely 2-adic *nonexistence* proof can exclude all such order-20 rules, even in the centered symmetric subcase. The square-moment congruences do not transfer to a nonsymmetric nodal polynomial, and no new unrestricted 17-site lower or upper conclusion follows. All arguments use source-level identities and short valuation comparisons only; no point/grid search, held source, Lean or shared edit was used.
