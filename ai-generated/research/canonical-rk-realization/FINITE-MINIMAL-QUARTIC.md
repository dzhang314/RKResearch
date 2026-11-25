# Minimal finite-horizon counterexamples, with a proper quartic Early cut

Full-series uniqueness does not turn paid data into a reconstruction. For each desired horizon $H$ and $p\ge7$, one can make two rational strictly explicit tableaux, each **minimal for its own full rooted series**, with the same $b,c$, exact order $p$, and matching rooted outputs through $H$, but different actual $F_0$ packet loss for the quartic mask

$$P(X)=X(X-1/8)(X-1/4)(X-3/8).$$

The discarded prefix is exactly the first four physical stages. No duplicate tree profile or invisible stage is used. There is an option with **all clocks distinct**. These methods are not claimed to minimize stage count among all tableaux of order $p$. The constructions use signed weights on several separate stages, cancelling only a finite initial segment of the rooted series; an explicit next-order tree sees the difference.

## 1. Minimal explicit core with literal $TP(c)=0$

Let $L=p+2$. Take an initial row of zero clock, followed by starters whose clocks are $1/8,1/4,3/8,u=1/2,v=5/8$ in that order. The starter with clock $x$ uses coefficient $x$ on the initial stage and no others. On these six stages $TP(c)=AP(c)=0$. Set $J(x)=\int_0^xP(t)dt$.

Take a first panel of $L$ distinct rational clocks $x$ not previously used, all nonzero, avoiding $u,v$ and the zeros of $J$. Use the coefficients

$$a_u=\frac{J(x)(v-x)}{(v-u)P(u)},\quad a_v=\frac{J(x)(x-u)}{(v-u)P(v)}$$

on starters $u,v$; use coefficient 1 on each of the three nonzero discarded-clock starters and choose the remaining origin coefficient to make row sum $x$. The three added coefficients do not affect $AP(c)$ nor $A(cP(c))$ because these starter clocks are roots. Thus the panel has $AP(c)=J(x)$, $A(cP(c))=xJ(x)$, and $A^2P(c)=0$ directly. On this panel $TP(c)=0$.

Append $p-1$ more panels, each with $L$ new, pairwise distinct nonzero rational clocks unused in earlier panels. In the row for new clock $x$, put $B_{xi}=\int_0^x\ell_i(t)dt$ on the immediately preceding panel, where $\ell_i$ interpolates its previous set of $L$ clocks. Each $B$ is invertible: a polynomial of degree $<L$ integrated from zero has degree $\le L$, and if it vanishes at $L$ distinct nonzero target clocks and at zero it is identically zero. Hence every preceding stage is the input of some nonzero edge into the new panel. Each new panel preserves $AP(c)=J(x)$ and $TP(c)=0$, via

$$xJ(x)-\int_0^x tP(t)dt-\int_0^x J(t)dt=0.$$

All row sums are as claimed and every dependency points strictly backward. The final panel has exact stage values $(n/\gamma(t))x^{n-1}$ for all trees of order $n\le p$: the leaf is always exact, and one interpolation panel advances the allowed tree height by one by integrating each child polynomial exactly. There are $p-1$ integration transfers after the first panel.

Put weight only on the final panel. On polynomials of degree $<L$, use the linear functional

$$g\mapsto\int_0^1 g(x)dx-\frac{[x^p]g}{p+1}+\tau[x^{p+1}]g$$

on its Lagrange basis. The final weights can all be made nonzero: each basis polynomial has nonzero leading coefficient, so only finitely many $\tau$ are forbidden. Moments through $p-1$ are paid and the degree-$p$ moment is zero rather than $1/(p+1)$. Since the final panel has the needed exact stage values, this core has exact classical order $p$. Distinct clocks imply every stage profile is different. Every panel stage feeds a weighted final stage by invertibility and backward induction. Each of the five starters feeds the first panel by its designated nonzero coefficients; the origin feeds the starters. Thus every core stage is visible, even though the nonfinal stages have zero direct output weight. The core has $6+p(p+2)$ stages and is already full-series minimal. In the exact check all panel nodes are chosen in $(1,2)$ and are distinct globally.

## 2. A genuinely minimal finite-order shell

Choose $N+1$ distinct nonzero rational parameters $z_i$ and barycentric weights

$$\lambda_i=\prod_{j\ne i}(z_i-z_j)^{-1}.$$

They satisfy $\sum_i\lambda_i z_i^k=0$ for $k<N$ and $=1$ for $k=N$, by taking the leading coefficient in the interpolation formula. In both variants append these $N+1$ output stages with weights $\lambda_i$ and clocks $y_i$, chosen outside the existing core. They reference only three earlier stages, namely $0$, the starter at $r=1/8$, and the starter at $u=1/2$. For $\theta=0$ or $1$, their coefficient row is

$$y_i e_0^T+z_i(e_r^T-e_0^T)+\theta z_i(e_u^T-e_0^T).$$

These rows do not feed any later row. Both variants have the same **individual** weights and clocks. On the shell $Ac=z_i(r+\theta u)$ and

$$TP(c)_i=\theta z_i(y_i-u)P(u).$$

Choose $y_i\ne u$ so this is identically zero in variant 0 and nonzero in variant 1. Earlier rows are unchanged, hence $T(P(c))$ vanishes outside the shell. The seed has positive rank one in both, and the actual first-step packet losses under the proper quartic cover are $1$ versus $0$. All shell weights are nonzero. If their clocks repeat they are distinguished by the actual order-three unary-stage column $Ac$; if the clocks are distinct this is automatic. Thus both tableaux are stage-minimal for their own full series by `PROOF.md`. No same-profile cancellation or deletion is possible.

**A small repeated-shell-clock construction.** Set $y_i=y=3/4$ for all shell stages. Each leaf child at a shell-rooted stage contributes the constant $y$. Each nonleaf child contributes an affine function in $z_i$, since its stage column on the earlier core does not involve the shell. A rooted tree of order $n\le 2N$ then has at most $N-1$ nonleaf children and its shell output vanishes by barycentric payment. The tableaux therefore agree in every rooted scalar through order $2N$. Choose $2N\ge\max(H,p+1)$ to preserve the core's exact order. At order $2N+1$, take a root with $N$ children, each the order-two unary tree. The difference between variants is exactly $(r+u)^N-r^N\ne0$, because the scalar shell polynomial is $z_i^N(r+\theta u)^N$.

**All clocks distinct.** Set $y_i=y+z_i$ with $y=3/4$ and, say, $z_i=i/(8(N+1))$, $1\le i\le N+1$. Every child contributes an affine function in $z_i$, including a leaf. All shell output vanishes through order $N$; at order $N+1$ the bush contributes identically in the two variants, and any other tree has at most $N-1$ children so still vanishes. Choose $N\ge p+1$ and $N+1\ge H$. At order $N+2$ a root with one order-two unary child and $N-1$ leaf children has shell stage value $z_i(r+\theta u)(y+z_i)^{N-1}$. The output difference is the leading coefficient difference, exactly $u=1/2$. All clocks are distinct, including between shell and core.

At $p=20,H=54$ the fixed-clock variant uses $446+28=474$ stages and the distinct-clock version $446+54=500$. Exact rational checks verify reachability and visibility by partition refinement, actual clock equality, quartic $TP(c)$ coordinates, and the first differing rooted witnesses at order 55. The analogous exact-order-8 versions directly check all 1,205 scalar trees through order 10. The order-20 arbitrary-shape equality follows by the polynomial proof above; no exhaustive order-54 tree enumeration was performed. In particular a native contraction containing a $TP(c)$ hole is zero on both variants whenever its fully filled order stays within their common horizon: it is an identical linear combination of known scalar trees, and vanishes on the first variant where $TP(c)=0$.

## 3. Minimal full-rank Euler witnesses as a second, independent point

The earlier finite horizon/full old 34-rank examples can themselves be made full-series stage-minimal. Use scaled left or right Euler extrapolation blocks $m=1,\ldots,M$ with $p$ positive rational scales $1/q_i$, where the $q_i>M$ are distinct primes. The first block on the first scale is $m=4$, providing a proper positive-degree mask. The rational step spacings $h=1/(q_i m)$ are distinct across microblocks. For positive grid clock $c$, the two stage columns $(c,Ac)$ determine $h$: for left Euler $2Ac=c^2-hc$, and for right Euler $2Ac=c^2+hc$. Thus every positive-clock stage has a different full profile. In DIRK all outputs have nonzero weight and there are no origins, so the raw tableau is minimal. In ERK the common zero-row origins form the only duplicated profile. Merging them gives one stage whose aggregate output is zero, since the extrapolation weights satisfy $\sum_m\omega_m/m=0$; it visibly feeds all later nontrivial left microsteps. Every other output is nonzero. The merged ERK is minimal and the first microblock’s four physical clocks remain the prefix.

The scaled extrapolation has exact order $p$ and its normalized tree output depends only on order through $M$. One can see this directly: on a fixed Euler microgrid, the order-$n$ stage polynomial in the micro-index has degree $n-1$ and leading coefficient $n/\gamma(t)$; summing output produces a polynomial in $1/m$ through degree $n-1$, whose constant coefficient is $1/\gamma(t)$. Extrapolate at zero in $1/m$ using $m=1,\ldots,M$. Blending $p$ scaled copies with interpolation weights at scale 1 multiplies each normalized tree output by the scale moment of exponent $n-1$, which is 1 for $n\le p$ and not 1 at $n=p+1$. Native one-hole decoration of a transported Volterra expression reads zero whenever the filled grade bound lies within $M$, because the formal integration model gives the Volterra defect zero and the common order factor does not change that. Native multi-hole contractions with one defect fill have the same bounded limitation. Merging zero-row origins preserves all tree expressions and the masked packet ranks since only equal coordinate copies are discarded. On a left/Euler microgrid $T=+hA$ and on a right grid $T=-hA$; direct tests use the actual commutator instead.

At $p=20,M=54$ the minimal ERK has 28,621 stages, and the minimal nonsingular DIRK 29,700. On both, all 34 old columns at quartic/terminal grade 14 are independent (two-hole 456-coordinate Gram determinants $738$ and $540\bmod1009$, respectively), all eight paid widths are full, and all native one-hole costs through 35 are blind. All denominators in the tested rational determinants are invertible modulo 1009. ERK had one merged zero coordinate per selected microgrid in the 456-row check; its mask vanishes at that shared origin, so repeated zeros change neither the displayed Gram nor the rank. These are finite-information examples, not candidate small-stage tableaux.
