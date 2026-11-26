# Measured cross-group feedback can beat the visible-clock count

Retain the setup of MASKED-DENSITY-GROWTH.md. This note gives a more refined exact certificate when actual physical suffix data are known. It keeps all groups simultaneously and does not add separate counts from nested cuts.

## Exact visible overlap of all paid linear words

For a budget \(r\ge0\), let \(\mathcal P_r\) be the span of pairs
\[
 \bigl(\boldsymbol\beta W(T,Y_S),\ \rho_W(y)\bigr)
       \quad\text{for words of length at most }r\text{ in }A,Y ,
 \qquad Y_S\coloneqq I-C_S .
\]
Here \(C_S\) is the inherited full clock diagonal on the suffix. The density \(\rho_W\) is computed from \(1\) by multiplication by \(y\) for each right \(Y\) and the zero-origin primitive \(J\) for each right \(A\), as defined in the companion note. For instance \(\mathbf b A^m\) has density \(y^m/m!\). The maximum density degree is \(r\). The exact scalar subspace supplied by those paid linear words on the physical prefix is
\[
       \mathcal V_r\coloneqq\{P\in K[y]_{\le r}:(0,P)\in\mathcal P_r\}.
                                                                    \tag{4}
\]
The zero in (4) is a simultaneous condition on the full suffix, not separate conditions with separately chosen coefficients on each co-clock block. Conversely every pair in (4) gives a true row already supported on the prefix, with exactly that density. This is the maximal certificate among these words; further genuine rooted annihilators may improve actual factorization.

At degree \(j=p-1-r\) let \(v_j\) be the exact scalar rank of integration against \(\mathcal V_r\) on \(K[x]_{\le j}\). The finite matrix uses the actual densities as rows; it never treats the union of their supports as a set of independent weights. If the prefix is nonsingular, a measured inequality is
\[
 s\ge L+
       \max_{\epsilon}\sum_{\substack{0\le j\le p-1\\j\equiv\epsilon\ ({\rm mod}\ 2)}} v_j
   = \max_{\epsilon}
       \left(B_\epsilon(p)+L-
       \sum_{\substack{0\le j\le p-1\\j\equiv\epsilon\ ({\rm mod}\ 2)}}(a_j-v_j)\right),
                                                                    \tag{5}
\]
where \(a_j,B_\epsilon(p)\) are the full scalar rank and parity sum in TELESCOPING-CUT-NULLITY.md. A known scalar or pure prefix rank can strengthen (5); with mixed prefix diagonal use the genuine kernel debits. Formula (5) is measured physical overlap, not a new payment of the same whole-tableau quadratic lower bound.

## Explicit certificates organized by consecutive groups

Suppose the suffix consists of \(g\) consecutive constant-clock groups, counting both endpoints and repeated labels in different groups. Define the actual cross-clock matrix
\[
                       H\coloneqq[C_S,T]=C_ST-TC_S .
\]
Its diagonal group blocks are zero, and all possible other entries strictly move forward in physical group index. Thus a row \(\boldsymbol\beta H^h\) can only read groups numbered at most \(g-h\) from the front. Even more accurately use the actually nonzero coefficient labels \(R_h\) of this row, allowing cancellation of paths. Choose a polynomial \(\chi_h\) with precisely one factor for each of those labels, or any superset verified from the physical graph. The raw row
\[
                 \mathbf b[C,A]^h\chi_h(Y)
\]
is physically supported before the suffix. Since the formal \([X,J_x]\) is \(J_x^2\), where \(J_x\) integrates from \(0\) to \(x\), its density is
\[
                     \frac{y^{2h}}{(2h)!}\chi_h(y).                \tag{6}
\]
It is paid at budget \(2h+\deg\chi_h\). Right multiplication by arbitrary additional powers of the actual \(Y\) gives its whole truncated polynomial ideal. Right multiplication by \(A\) supplies the additional primitive growth in the companion note. These are certified subspaces of the single measured space (4).

There is a simple exact rule for overlap between the polynomial ideals in (6). Ignore their nonzero normalization scalars and call their generators \(P_h\), with degrees \(d_h\). Starting at \(P_0\), let \(G_h\) be the greatest common divisor of \(P_0,\ldots,P_h\). Suppose the previous generators already span every multiple of \(G_{h-1}\) of degree at most \(r\). Put \(Q_h=G_{h-1}/G_h\). When \(Q_h\) is nonconstant and \(r\ge d_h+\deg Q_h-1\), the new generator extends the span to exactly every multiple of \(G_h\) of degree at most \(r\). Indeed \(P_h/G_h\) is invertible modulo \(Q_h\); its multiples by polynomials of degree less than \(\deg Q_h\) give every residue class. Subtract one of these from any desired multiple of \(G_h\), using at most degree \(r\), and the remainder is a multiple of the old generator \(G_{h-1}\), hence already paid. If \(Q_h\) is constant the old span is already the desired one. This proves the exact truncated rule, including when several seen labels disappear simultaneously or when the actually supported masks are not nested.

For a completely physical but nonmeasured instance, take \(\chi_h\) to use the distinct labels in the first \(g-h\) groups. One label can disappear at each step, and the degrees \(2h+\deg\chi_h\) increase by at least one. Hence the full-gcd conclusion at step \(h\) is paid as soon as this degree is paid. The gcd consists of the remaining nonzero labels of the first \(g-h\) groups, and a single factor \(y\) if the original mask has the endpoint label. This last factor comes from the original mask, since every marked row with \(h>0\) has at least two factors of \(y\). If the endpoint was inferred by using a superset of visible labels, do not credit its removal without a narrower actual mask. With no endpoint labels, this gives scalar debit at most \(\min(r+1,(2g-r)_+)\), and thus \(s\ge Q(p)+L-g(g+1)/2\) on a nonsingular prefix. The actual visible-label theorem often improves \(g\) to \(q\); the measured generator and quotient rules can improve either bound when raw tail support truly drops early.

The endpoint factor left by such a density calculation need not be an actual lost channel. Once the needed positive densities are paid, the appropriate next step is the actual suffix orbit/overlap criterion in the companion note, or the full matrix (4). Postulating independent shape per block cannot eliminate a scalar density whose raw tails still overlap.

## Internal repeat does not give an independently additive bonus

There is a genuine small nonsingular DIRK counterexample to applying the one-trailing-group bonus separately to every internal block. Use the known order-six uniform implicit-midpoint extrapolation, with one-, two-, and three-substep branches and branch weights \(1/24,-16/15,81/40\). Every branch is lower triangular, has diagonal \(1/(2n)\) on its \(n\) substeps, and clock labels \((i-1/2)/n\). The outputs have the indicated branch weights divided by \(n\) on its substeps. The order-six identity is the standard verified nonsingular midpoint equality: symmetry gives the formal logarithm of an \(h/n\) midpoint step as \((h/n)F+(h/n)^3F_3+(h/n)^5F_5+O(h^7)\). Repeating it \(n\) times and expanding through degree six gives a polynomial of degree at most two in \(1/n^2\), with constant term the exact Taylor step. The displayed weights are its Lagrange evaluation at zero. This is an ordinary rooted order-six method, as also recorded in central_commutator_and_odd_dirk_20261122.md.

The independent branches may be ordered so that the chronological clocks are
\[
                          (1/4,3/4,1/6,1/2,1/2,5/6).
\]
Both \(1/2\) rows are physically present: one is the single step of the first branch, the other is the middle step of the third. Their order in the list respects all actual donors. This is a nonendpoint internal double group with \(s=6=Q(6)\). The subsequent \(5/6\) receiver can see the third-branch \(1/2\) input, and it does not justify an independent co-clock-tail refund for the earlier block. Hence the terminal hypothesis, or an actual overlapping support/coupling certificate such as (4), cannot be dropped. The counterexample uses nonsingular **mixed** DIRK; it does not settle the separate possible extra rigidity of common-diagonal tableaux.

The results impose uniform and measured shape restrictions, not an unrestricted stage count or a claim that all minimizing tableaux have a favorable suffix.
