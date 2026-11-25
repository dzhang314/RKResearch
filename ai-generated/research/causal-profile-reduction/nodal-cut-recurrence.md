# An all-order clock cutoff for nonsingular triangular Runge–Kutta methods

Let $A$ have any reviewed rooted-tree order $p\ge1$ over a field $K$ and be lower triangular with all diagonal entries nonzero. No assumption on the signs or zeros of the output weights, no stage-minimality hypothesis, and no ordering on $K$ are needed. Let $x=A\mathbf1$, $C=\operatorname{diag}(x)$, $\beta=b^{\mathsf T}$, and $R=CA-AC-A^2$. Denote by $B(m)$ the existing [nonsingular parity stage floor](../../lean/RKCert/ReviewedNative/NonsingularDIRKStageFloor.lean) at positive order $m$; below we use $B(m)=0$ when $m\le0$, not a new convention for the implementation at order zero.

**Clock cutoff.** Before any suffix with only $q$ distinct clocks among its *individually nonzero* output weights there must be at least $B(p-2q)$ earlier stages. After any prefix with only $q$ distinct *physical* clocks there must be at least $B(p-2q)$ later stages. In particular these are counts outside the specified segment, not bounds needing correction for slack above the stage floor. An inactive output weight cannot be counted as a new suffix clock; cancelling active weights at the same location do not delete that clock. For any split with $q_H$ different physical clocks in the head and $q_T$ different active clocks in the tail, both bounds apply simultaneously:
$$
 \#\mathrm{head}\ge B(p-2q_T),\qquad
 \#\mathrm{tail}\ge B(p-2q_H).
$$
For instance a nonsingular order-nine method has at least $B(5)=5$ predecessors of any tail with just two active clocks. At order ten that count is $B(6)=6$. No particular higher-order tableau was used.

## 1. Independent primal and dual packets

For $0\le j\le p-1$ put $w_p(j)=1+\min(j,p-1-j)$. At any degree $0\le r\le p-1$, the following are two separate independent families, one of columns and one of covectors:
$$
 R^k x^a,\qquad \beta C^a R^k,\qquad
 0\le 2k\le r,\quad 0\le a<w_p(r-2k).
 \tag{1}
$$
Here $x^0=\mathbf1$. In both families their number is exactly the parity census $\nu_p(r)=\sum_{k=0}^{\lfloor r/2\rfloor}w_p(r-2k)$. Thus $B(p)$ is the maximum of the last odd and even parity sums, equivalently the maximum over all affordable $r$.

For completeness, the proof applies at arbitrary order. Use the genuine elementary and defect flags $E_j,F_j$. The reviewed tree identities give $RE_j\subset F_{j+2}$ in budget, $F_j\subset E_j$, and $\beta C^a F_j=0$ if $a+j+1\le p$. Also $R$ is invertible since its diagonal is $-A_{ii}^2$. In either family, growing from degree $r-2$ multiplies all old columns by $R$ on the left or all old rows by $R$ on the right, retaining their independence. Add the affordable pure columns or pure rows of degrees $0,\ldots,w_p(r)-1$. The old shifted packet has zero pairing with every matching pure test on the opposite side: in any such pairing at least one physical $R$ puts the evaluated column in the defect flag, and the final total cost is at most $r+w_p(r)-1\le p-1$. The pure-to-pure square Hankel matrix is nonsingular by the paid Cauchy determinant for $\beta x^h=1/(h+1)$. Hence the ranks add. The same pure Hankel argument starts at degree zero or one. In particular minuscule or zero weights are not singularities of the proof.

## 2. Actual witness packet on one side of the cut

More generally choose any nonzero polynomial $P$ over $K$ of degree $q$ and put $m=p-2q>0$. For every $0\le r'\le m-1$, the two masked families
$$
 R^k P(C)x^a,\qquad \beta P(C) C^a R^k,\qquad
 0\le 2k\le r',\quad 0\le a<w_m(r'-2k)
 \tag{2}
$$
are separately independent. Indeed use (1) with degree $r=r'+q$. At layer $k$ put $h=r'-2k$; then
$$
 w_p(h+q)=q+w_m(h).
$$
Consequently $P(X)X^a$ is among the permitted polynomials in the original block. Within a block these masked polynomials are independent since $P$ is nonzero; the original blocks were already independent of one another. This argument does not assume a positive weighted moment for $P^2$, and it never reinterprets masked weights as another RK method.

For a terminal segment take $P(X)$ to be the product of $X-\xi$ over its distinct active clocks (the empty product is one). Then $\beta P(C) C^a$ vanishes on the segment's coordinate subspace. This subspace is $R$-invariant, so all the right-multiplied covectors in (2) also vanish there. They are independent covectors in the first $\#\mathrm{head}$ coordinates. Choose $r'$ maximizing the effective parity count to obtain $\#\mathrm{head}\ge B(m)$. This proof works for any $R$-invariant coordinate subset in lieu of the suffix, with the number of outside coordinates on the left. Dually, for a prefix take its physical-clock nodal polynomial; $P(C)x^a$ vanishes on the prefix, and the remaining coordinate subspace is $R$-invariant. Now use the column family in (2). This proves both cutoffs.

**Equality certificate.** If a cutoff is attained at the chosen segment and $p>2q$, the displayed optimal masked packet is a basis for the *whole* complementary coordinate space (its dual in the terminal case). Thus it recovers arbitrary data on the paid side of the cut. This is stronger than the numerical cutoff alone, and applies whether or not the entire tableau attains its global stage floor. At $(7,8)$ and $(8,10)$ setting $q=2$ recovers the last-seven and last-eight active-clock obstructions in the [causal profile paper](README.md). The [indexing check](check-nodal-cut.py) verifies the block widths, counts, and polynomial coefficient embeddings exactly; it does not construct any tableau.
