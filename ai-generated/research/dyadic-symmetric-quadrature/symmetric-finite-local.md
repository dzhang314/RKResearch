# Sharp dyadic bounds and finite-prime local attainability for symmetric rules

There is no real or prime-local nonexistence obstruction to the **centered symmetric 17-site order-20** support. More precisely, for any finite set of primes, one rational nodal polynomial gives 17 distinct signed interval sites over \(\mathbb R\) and splits with the same nonzero rational weights over each chosen prime field \(\mathbb Q_\ell\). One reflected pair may fail to be rational: indeed for every prescribed finite set there is such a polynomial that fails to split at an omitted prime. This proves finite local attainability, not rational attainment.

The argument also establishes the exact symmetric support floors over \(\mathbb Q_2\) through order 20 and attains all those floors jointly over the reals and any finite list of other primes.

## 1. The square-moment equations and the dyadic floor

Put \(Y=2X-1\), \(T=Y^2\); the centered uniform probability functional has \(L(Y^{2j})=1/(2j+1)\) and vanishing odd moments. A centered symmetric support with \(r\) reflected pairs and center indicator \(e\in\{0,1\}\) has nodal polynomial
\[
    P(Y)=Y^e H(Y^2),\qquad H(T)=\prod_{i=1}^r(T-a_i^2).
\]
Its sites are distinct when the magnitudes \(a_i\) are nonzero with distinct squares. When \(m=2r+e\le p\), the first \(m\) moments fix the weights by Vandermonde, hence the weights inherit reflection symmetry. A paid odd \(p\) then automatically pays degree \(p\) too. Write \(2N=2\lceil p/2\rceil\), and define
\[
 \alpha=1+2e,\qquad M_\alpha(T^j)=1/(2j+\alpha),\qquad t=N-r-e .
\]
Division by \(P\) gives \(t\) reduced nodal equations \(M_\alpha(T^jH)=0\), \(0\le j<t\), for the first \(2N\) moments. Exact order \(2N\) means the next row is nonzero. These conditions apply to a rule symmetric about the integration midpoint; they do not presume the roots of a general nonsymmetric polynomial are paired.

Use \(Z=T-1\). At 2 every square factor, after a harmless scalar for each nonintegral magnitude, has one of the forms \(T-\eta\), \(Z-\epsilon\), \(1-\theta T\), with \(\eta,\theta\in4\mathbb Z_2\) and \(\epsilon\in8\mathbb Z_2\). Let \(b\) count the middle (unit square) factors. The elementary finite-difference identity
\[
 M_\alpha(T^c Z^d)=
 \frac{(-1)^d 2^d d!}{\prod_{j=0}^{d}(\alpha+2c+2j)}
\]
follows inductively by subtracting the moment at \(c\) from that at \(c+1\). Its valuation is \(v_d=d+v_2(d!)\). In \(M_\alpha(T^j Z^\ell H)\) the unperturbed exponent is \(d=b+\ell\); using \(h\) corrections from unit factors costs at least \(3h+v_{d-h}\), while any other correction adds at least two. Through order 20, needed \(d\le N-e-1\le9\). The only \(d\le9\) where \(v_d\) is not strictly less than \(\min_{h\ge1}(3h+v_{d-h})\) are 4 and 8:
\[
\begin{array}{c|rrrrrrrrrr}
d&0&1&2&3&4&5&6&7&8&9\\\hline
v_d&0&1&3&4&7&8&10&11&15&16\\
\min_{h\ge1}(3h+v_{d-h})&\infty&3&4&6&7&10&11&13&14&17
\end{array}
\]
The paid rows are equivalently the first \(t\) rows in the \(Z\)-basis. Since two consecutive exponents cannot both be exceptional, \(t\le1\). If \(t=1\) then \(b=4\) or 8, so \(r\ge4\), and the next row is nonzero because \(b+1\) is 5 or 9. A zero-weight pair or center would reduce the support until there were at least two reduced rows for the same order, so every distinct one-row support here is active over \(\mathbb Q_2\).

The resulting lower floors on support, sharp over \(\mathbb Q_2\), are
\[
\begin{array}{c|cc}
2N&\text{without center}&\text{with center}\\\hline
2,4,6,8&2N&2N-1\\
10&8&9\\
12,14,16,18,20&2N-2&2N-3 .
\end{array}
\]
At \(t=0\), small distinct rational magnitudes give ordinary interpolation, active since its cofactor numerators tend to nonzero monomial moments. The one-row attainment proof follows. The table gives rational lower bounds, not rational upper bounds at \(t=1\).

## 2. Exhaustive forced-square chart and real interval feasibility

For a one-row support fix \(r-1\) magnitudes and their square polynomial \(K\). The last squared magnitude is forced by \(M_\alpha(K(T-s))=0\):
\[
                  s=\frac{M_\alpha(TK)}{M_\alpha(K)} .
\]
For rational fixed magnitudes there is no overlooked singular completion in the stated range. If \(M_\alpha(K)=0\), the dyadic test forces its unit count to be 4 or 8, whereas the adjacent row \(M_\alpha(TK)=M_\alpha(ZK)\) cannot vanish. So every rational one-row support through order 20 is covered by this chart, regardless of which pair is taken last.

For real interval feasibility take the fixed magnitudes distinct, positive and sufficiently near zero. Then \(K\to T^{r-1}\) and \(s\to A/(A+2)\in(0,1)\), \(A=2(r-1)+\alpha\). There are no collisions, and the resulting weights and first defect are nonzero on this real open. To check this explicitly, write \(H_i=H/(T-a_i^2)\). The weight at either member of an old or new pair is \(M_\alpha(H_i)/(2H'(a_i^2))\) when \(e=0\), and \(M_\alpha(H_i)/(2a_i^2H'(a_i^2))\) when \(e=1\). The center weight when present is \(M_1(H)/H(0)\). The old pair and center numerators tend to
\[
             \frac1A-\frac{A/(A+2)}{A-2}
            =-\frac4{A(A+2)(A-2)}\ne0.
\]
The new pair's numerator tends to \(1/A\), and \(M_\alpha(TH)\) tends to \(4/((A+4)(A+2)^2)\ne0\). For rational fixed magnitudes all these weight formulas depend only on rational squared nodes. Thus they give the same active rational weights in every field where the forced last square splits. No positivity is claimed.

## 3. Joint local realization

**At 2.** For \(r\ge4\), choose three of the fixed magnitudes to be units with squares \(1\bmod16\) and the others to be nonunits. Then \(M_\alpha(K)\) and \(M_\alpha(ZK)\) have valuations 4 and 7 in the normalized product: the higher unit congruence makes the leading valuation strict also at exponent 4. The last square is \(s\equiv9\bmod16\), an actual \(\mathbb Q_2\)-square distinct from all fixed squares. When \(r\ge8\), choose instead seven fixed units with squares \(1\bmod32\). The same argument at exponents 7 and 8 gives valuations 11 and 15, so \(s\equiv17\bmod32\) is likewise an actual \(\mathbb Q_2\)-square distinct from the fixed ones. Thus both permitted unit counts are achieved where available. At \(r=8,\alpha=3\) (order 20 on seventeen sites), any rational solution must have one of these counts; more finely, the sums of the unit squares are \(12\bmod16\) or \(24\bmod32\), respectively. To see these congruences, put \(S=\sum_{\rm unit}(a_i^2-1)/8\). Expansion to the first nontrivial digit gives \(M_3(H)/2^7\equiv1+S\bmod2\) at count four, and \(M_3(H)/2^{14}\equiv2+3S\bmod4\) at count eight. The coefficient \(3\bmod4\) in the latter comes from \(7!/2^4=315\) and a denominator of eight consecutive odd terms in steps of two, whose product is \(1\bmod4\).

**At every odd prime \(\ell\).** Let \(c\) fixed magnitudes approach 0, \(k-c\) approach 1, and \(r-1-k\) grow \(\ell\)-adically in magnitude. Normalize the factors of the last group so that they approach 1. Then \(K\), up to its harmless scalar, tends to \(T^c(T-1)^{k-c}\), and the forced \(s\) tends to
\[
                   \frac{\alpha+2c}{\alpha+2k+2},
                  \qquad 0\le c\le k\le r-1.
\]
This ratio follows immediately from the finite-difference identity. If \(\alpha=3\), use the four pairwise coprime odd integers \(3,5,7,11\); if \(\alpha=1\), use \(1,3,5,7\). At least three are units at \(\ell\). Take three in increasing order \(U<V<W\). Each ratio \(U/V,V/W,U/W\) is of the displayed form with \(k\le3\); moreover their product is \((U/W)^2\). Three nonsquare units cannot have square product modulo an odd prime, so one of the three ratios is a unit square in \(\mathbb Q_\ell\). Perturb the fixed magnitudes to distinct finite nonzero values close enough to the indicated local limit to preserve the square class. The forced square is separated from the old squares because its limit is neither 0 nor 1 nor infinity. This requires no field search.

For any prescribed finite set of primes, the real open in Section 2 and these local open conditions can be met by a **single rational tuple of fixed magnitudes**, by weak approximation in each coordinate (Chinese remainder approximation at the finite places and rational approximation at the real place). Then the same rational \(K\) and \(s\) give an active exact-order rule over all selected fields. Taking \(t=1\) proves every sharp dyadic floor in the table is jointly realizable in this sense, including precisely 17 sites at order 20.

## 4. Exact distinction from rational attainment

For a fixed rational \(K\) with admissible real data, the last pair is rational if and only if \(s\) is square at **every** prime for that same \(K\): positivity and even valuations at all primes are exactly the rational-square condition. A tuple allowed to vary with the set of primes does not supply one such \(K\).

In fact any fixed finite list \(S\) of primes has false positives in the actual seven-pair chart at order 20. Choose an odd positive integer \(n\equiv13\bmod60\) coprime to every prime of \(S\) (use Chinese remainders). Quadratic reciprocity gives the Jacobi symbol \((15/n)=-1\), so a prime divisor \(\ell\notin S\) has \((15/\ell)=-1\). At this omitted prime force all seven fixed magnitudes large, making \(s\) approach \(3/5\), a nonsquare unit at \(\ell\). Weak approximation as above can enforce this open nonsplit condition along with the real interval condition and split conditions at every prime of \(S\). It follows that there are actual positive, nonrational candidate squares passing any predetermined finite set of prime tests, with all cofactor weights nonzero. This is not a proof of failure of a Hasse principle for the variable-support problem, since we do not know whether it has a global rational point.

An additional simple necessary 19-adic condition for rational 17-site order 20 is that at least one magnitude be nonintegral at 19: if all were integral, only the leading term \(1/19\) in \(M_3(H)\) would be nonintegral. If exactly one is nonintegral, take it last; \(M_3(TK)\) has valuation \(-1\) at 19, so \(M_3(K)\) must have positive odd valuation for the ratio to be a square. These are pointwise filters, compatible with local attainability.

Equivalently, if two magnitudes \(x,y\) are left free after six, set \(M_j=M_3(T^jH_6)\). At \(M_1\ne0\), the actual equation is
\[
      xy=w,\qquad x^2+y^2=\Sigma(w),\qquad
      \Sigma(w)=\frac{M_0w^2+M_2}{M_1}.
\]
It requires **both** \(\Sigma(w)+2w\) and \(\Sigma(w)-2w\) to be squares, not just that \(\Sigma(w)\) be a sum of two rational squares. The converse follows by taking their square roots as \(x+y\) and \(x-y\). For two distinct nonzero interior magnitudes the equivalent strict real inequalities are \(0<|w|<1\) and \(2|w|<\Sigma(w)<1+w^2\), with old-site collisions excluded. Thus the discarded nested-circle recipe is not a general rationality criterion. The local construction above uses the unconstrained seven-pair chart, and its scope is independent of that recipe.

There is no global rational 17-site witness, global nonexistence claim, positivity claim, or RK stage conclusion in this note. The construction and proof use exact identities, valuation comparisons, and weak approximation only.
