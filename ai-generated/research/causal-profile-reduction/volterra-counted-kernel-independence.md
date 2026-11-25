# Paid order does not determine the counted Volterra kernel

This is a mathematical counterexample and a packet-level sufficient condition, with exact rational checks. Neither is a new Lean theorem or an unrestricted stage bound. The [separate Lean-checked four-clock certificate](multiclock-mask-cut.md#6-a-separate-lean-checked-four-clock-certificate-at-order-20) still has its stated whole-side kernel premise.

## Same clocks, weights and order, different kernels

For \(c=A\mathbf1\), the reviewed [Volterra step](../../lean/RKCert/ReviewedNative/NonsingularDIRKStageFloor.lean) is \(T=DA-AD-A^2\), \(D=\operatorname{diag}(c)\). If \(A\) is lower triangular, so is \(T\), with diagonal \(-a_{ii}^2\). For a cut after the first \(k\) stages, the two counted operators are \(T\) on suffix-supported columns and \(T^*\) on prefix-supported covectors. Each is injective exactly when every diagonal entry of \(A\) on its own counted side is nonzero.

Start with any lower triangular tableau. Replace each stage by a consecutive group of copies. Let \(P\) replicate coordinates, \(E\) select the first coordinate in each group, and \(r(j)\) denote the first copy of a stage whose nonfirst copy is \(j\). Fix weights \(\widehat b\) summing to the old \(b\) within each group. On this fixed expanded stage set set
\[
\widehat A_\delta=PAE+\sum_{j\ {\rm nonfirst}}\delta_j\,e_j(e_j^*-e_{r(j)}^*).
\]
This is lower triangular and has \(\widehat A_\delta P=PA\), \(E\widehat A_\delta=AE\), and \(\widehat c=Pc\). Replication preserves the vector of ones and coordinatewise products. The rooted-tree stage recursion therefore gives \(\widehat\Phi_t=P\Phi_t\) for every tree, and \(\widehat b^*P=b^*\) preserves every tree output. All moments and masked Hankels stay fixed, as do the individual clocks and weights. For an active-suffix cover, give zero-weight groups only zero shares. Nonzero old weights can be split into nonzero shares over \(\mathbb Q\).

In the decomposition \(PV\oplus\ker E\), the two summands are invariant. On the extra coordinates, \(\widehat A_\delta\) is diagonal with entries \(\delta_j\), and \(\widehat D\) is diagonal too. Thus \(\widehat T_\delta\simeq T\oplus\operatorname{diag}(-\delta_j^2)\). Cutting between groups preserves the literal discarded clock sets. The suffix column kernel increases by the number of zero \(\delta_j\) among its extra coordinates, and the prefix dual kernel increases by the corresponding number in its own extra coordinates. These choices are independent at the same expanded stage count.

### Exact rational examples

For any positive \(p\), use block-diagonal implicit-Euler substep blocks \(m=1,\dots,p\), with \(m\) stages, \(A_{j\ell}=1/m\) for \(\ell\le j\), and individual weights \(\omega_m/m\), where
\[
\omega_m=(-1)^{p-m}\frac{m^{p-1}}{(m-1)!(p-m)!}.
\]
These are the Lagrange weights at zero on \(z_m=1/m\). For a tree of order \(n\), the block output before \(\omega_m\) is \(\Omega_t(m)/m^n\), counting weakly ordered vertex labels in \(1,\ldots,m\) with each child at most its parent. Grouping by the number of distinct labels shows \(\Omega_t(m)\) is a polynomial in \(m\) with zero constant and leading coefficient \(1/\gamma(t)\), where \(\gamma(t)\) is the tree factorial: on \(n\) distinct labels, interleaving the child orderings counts \(n!/\gamma(t)\) linear extensions. Thus the quotient is a polynomial in \(z_m\) of degree at most \(n-1\), and interpolation gives the reviewed order-\(p\) conditions. At order \(p+1\) the tall tree has nonzero extrapolation error \((-1)^{p+1}/(p+1)!\). Every original diagonal and individual weight is nonzero.

For \(p=20\), put the four-stage block first or, in a separate tableau, last. The four discarded clock values are \(1/4,1/2,3/4,1\). Three extra copies on the counted side give 213 stages. The [exact checker](check_volterra_counted_kernel.py) computes local kernel dimensions \(0,1,3\) in both separate orientations while the eight paid Hankel ranks remain \(1,\ldots,8\); it uses the actual step matrix and exact rational elimination. See its [recorded output](volterra-counted-kernel-check.txt). Reproduce it with `python3 check_volterra_counted_kernel.py`; no external packages are needed.

**Distinct clocks do not rescue the implication at finite order.** To get distinct base clocks, take \(p+2\) scaled copies of each Euler block with globally different rational scales \(\lambda\in(1,1+1/(2p^2))\), and use Lagrange weights at \(\lambda=1\) in each block. This removes the factor \(\lambda^n\) in a tree output for \(n\le p+1\). Different reduced clock fractions \(j/m\) cannot collide under these scales; equal fractions separate. Insert \(p+1\) distinct new counted clocks \(\theta_j\) outside the old clock set, with unchanged nonzero signed weights \(1/\prod_{h\ne j}(\theta_j-\theta_h)\), all feeding from the same earlier stage with coefficient \(\theta_j-\delta\) and with diagonal \(\delta\). No old row uses a new column. For fixed \(\delta\), the elementary value at a new row is a polynomial in \(\theta_j\) of degree at most \(n-1\) for an order-\(n\) tree: each child of order \(r\) contributes a polynomial of degree at most \(r\). The signed weights annihilate all polynomials of degree below \(p\) by the leading coefficient in Lagrange interpolation. Thus all paid tree outputs and all clocks and weights stay fixed across \(\delta\). Taking \(\delta=0\) gives \(p+1\) extra counted nullity (all those columns vanish), whereas \(\delta=1\) leaves the counted block injective. This variant uses signed, not necessarily positive, weights.

## An actual rank test and a weaker stage-count condition

On a counted space of dimension \(N\), let \(S\) be the actual masked polynomial seed map and \(C\) the actual polynomial probes through degree \(N-1\). The matrix \(H_1=CT_*S\), with \(T_*\) the restricted step, certifies injectivity if it has rank \(N\). If the unshifted \(H_0=CS\) is nonsingular, the rank deficit \(N-\operatorname{rank}H_1\) is exactly the local nullity. This uses independent actual data: all fully paid pairings \((b\odot c^{[i]})^*T c^{[j]}\) vanish when \(i+j+3\le p\). The three tree contributions, after factoring out \(1/(i+j+3)\), are \(1/(j+1)\), \(1/(j+2)\), and \(1/[(j+1)(j+2)]\); their difference is zero. A mask spends its degree in the same budget.

For a **stage count** rather than full-side injectivity, the reviewed [local one-charge rank step](../../lean/RKCert/ReviewedNative/PaidMaskOneCharge.lean) already gives
\[
\dim F_{r+2}\ \ge\ c_{r+2}+\dim F_r-\dim(F_r\cap\ker T_*),
\]
where \(F_r\) is the actual parity packet and \(c_r\) its fresh paid readout credit. Thus it suffices to check that the step is injective on the transported packets, even with kernel vectors elsewhere in the counted side. More generally, a certified upper bound \(z_r\) on that packet loss gives the clipped recursion \(R_{r+2}=c_{r+2}+\max(R_r-z_r,0)\) with initial credits \(R_0=c_0\), \(R_1=c_1\) where present. Each bound follows by rank-nullity on the transported packet and the separating fresh readout.

For the order-20 four-clock rank credit, the even chain ends at grade 14. To keep the full 28 credit, injection on the packets at grades \(0,2,4,6,8,10,12\) suffices; no injectivity on the final packet is needed. The stage count still needs the relevant actual chronological cover. This packet criterion is a mathematical consequence of the local step, not a change to the hypotheses of the linked Lean-checked theorem.
