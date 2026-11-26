# Exact chronological criterion for deleting a Runge–Kutta cohort

The criterion separates preservation of the retained stage vectors from preservation of the final output. The companion [causal reduction proof](CAUSAL-ROOTED-COHORT-REDUCTION.md) gives examples at arbitrary order.

## Exact test without assuming one common cohort profile

Let \(D\) be the stages to delete and \(R\) the stages to retain, in their original orders. Write \(\widehat A=A_{RR}\), \(\widehat{\mathbf b}=\mathbf b_R\), and define
\[
 B\coloneqq A_{R,D},\qquad
 V\coloneqq A_{D,R},\qquad
 M\coloneqq A_{D,D}.
\]
For a rooted tree \(t\) let \(u_t\coloneqq\boldsymbol{\Phi}_t(\widehat A)\). Define a vector \(z_t\) on the deleted coordinates by the rooted recursion
\[
 z_\bullet\coloneqq\mathbf 1_D,\qquad
 z_{[t]}\coloneqq V u_t+M z_t,\qquad
 z_{t\#v}\coloneqq z_t\odot z_v.
\]
Equivalently \((u_t,z_t)\) is the actual tree vector on the same tableau with only the block \(B\) zeroed out. This defines \(z_t\) even if the intended deletion is invalid.

**Exact finite test.** The principal deletion preserves every retained stage tree vector through size \(p\) if and only if \(B z_t=0\) on all trees of size \(\le p-1\). It preserves those retained vectors **and** every original output read through size \(p\) if and only if, in addition, \(\mathbf b_D\cdot z_t=0\) for every tree of size \(\le p\).

To prove sufficiency, induct on tree size. A retained unary extension has the same value on the two arrays because the original \(B\)-term is zero on its child of size at most \(p-1\); the deleted rows have the same \(V,M\) and the same lower-order inputs. Rooted sums just multiply coordinates. Thus the original vectors are exactly \((u_t,z_t)\) through size \(p\), and the remaining read difference is the stated cohort contribution. Conversely, if retained profiles agree through \(p\), their agreement forces the original deleted profiles to be \(z_t\) recursively through \(p\). Equality for each retained unary extension \([t]\) gives \(B z_t=0\) through size \(p-1\); the output difference is then \(\mathbf b_D\cdot z_t\) through size \(p\). This proves necessity in the specified stage-preserving problem, not a characterization of every possible deletion that happens to preserve only the order.

The test consists of polynomial identities over any commutative unital coefficient ring. Inherited ordinary denominator-cleared \(\mathrm{HasOrder}\ p\) follows from equality of reads, so no real or field property is needed for this deletion step. A lower triangular principal submatrix remains lower triangular, strict triangularity is retained, and a strict SDIRK principal submatrix keeps the original nonzero common diagonal. Zero contributions in \(b\) alone are insufficient when the outgoing block can see a deleted vector.

## A balanced cohort: the concrete incoming contrast criterion

Assume the actual indicator is balanced:
\[
 A\mathbf1_D=a\mathbf1_D,\qquad \mathbf b\cdot\mathbf1_D=0,
\]
where \(\mathbf1_D\) is extended by zero outside \(D\) in these two equations. The block meanings are \(B\mathbf1_D=0\), \(M\mathbf1_D=a\mathbf1_D\), and \(\mathbf b_D\cdot\mathbf1_D=0\). For the first physical \(i_0\in D\), lower triangularity gives \(a=A_{i_0i_0}\), and in SDIRK this is the common diagonal. The same incoming comparison works regardless of whether the later cohort rows couple internally; only the internal row sums are used.

Let \(U_k\) be the actual span of \(\boldsymbol{\Phi}_t(\widehat A)\) through tree size \(k\), with \(U_0=0\). In reviewed grade notation \(U_k=T_{k-1}(\widehat A)\) for \(k\ge1\). Set
\[
 \Delta_i\coloneqq A_{i,R}-A_{i_0,R}\qquad(i\in D).
\]
The cohort's original stage-derivative weights are constant on \(D\) through tree size \(q\) **if and only if** \(\Delta_i\) annihilates \(U_{q-1}\) for each \(i\in D\).

Indeed, collapse the cohort to the coordinate of an auxiliary representative with the incoming row \(A_{i_0,R}\), diagonal \(a\), and no outgoing entries into \(R\). It is lower triangular if the representative is placed at the original first cohort row. The lift \(P(u,z)=(u,z\mathbf1_D)\) preserves the unit and coordinatewise products. On an input of this form the difference between original and representative matrix actions at any \(i\in D\) is exactly \(\Delta_i u\); there is no term from the internal block because all its row sums are \(a\). The retained difference is zero by \(B\mathbf1_D=0\). This proves sufficiency by rooted recursion, or observes that the first failing incoming tree contrast on size \(h\) is first visible at the actual unary root of size \(h+1\). Conversely, if actual cohort profiles agree through \(q\), each retained extension with child size \(\le q\) ignores the common cohort component, and the retained profiles agree with \(\widehat A\) through \(q+1\). Comparing the cohort values of \([t]\), \(|t|\le q-1\), now gives \(\Delta_i u_t=0\) because their common child and internal sums have canceled.

Thus full individual annihilation through \(U_{p-1}=T_{p-2}\) gives equal cohort profiles and safe deletion through \(p\), but one does **not** need it as a general condition on the last order.

**Sharper version for \(p\ge2\).** It suffices that the individual contrasts annihilate \(U_{p-2}\), and that the single aggregate row
\[
 \mathbf b_D^{\rm row}V=\sum_{i\in D} b_iA_{i,R}
\]
annihilate \(U_{p-1}\). Under the first hypothesis, the aggregate condition is necessary and sufficient for equality of the final reads at order \(p\). In fact the first hypothesis gives a common cohort profile through size \(p-1\), and so all retained profiles through size \(p\) are unchanged. Among trees of size \(p\), a nonunary tree has children of size at most \(p-2\), making its cohort coordinate a product of common lower-order coordinates. Its total cohort output therefore vanishes. For a unary tree \([t]\) of size \(p\), its cohort vector is \(V u_t+a z\mathbf1_D\) for a shared child value \(z\), whose output is exactly \((\mathbf b_D^{\rm row}V)u_t\). Through lower sizes that aggregate already vanishes by the individual hypotheses and zero total. This proves the exact last-order condition.

Special cases clarify the respective orders:
- If the cohort output is coordinatewise zero, only the size-\((p-2)\) individual contrast tests are needed under balancing; the more general \(Bz_t=0\) condition can be weaker still.
- For a cohort of exactly two rows with opposite nonzero weights, the aggregate top row is a nonzero scalar multiple of their incoming contrast; full individual orthogonality through \(U_{p-1}\), or equivalently full agreement through size \(p\), is then necessary for the stage-preserving deletion once agreement through \(p-1\) is granted.
- If both \(B=0\) and \(\mathbf b_D=0\), there is no need for an equal-clock, eigenline, or contrast assumption at any order.
- If \(A u=a u\) and \(\mathbf b\cdot u=0\) for a supported vector whose nonzero amplitudes are unequal, those identities do not pay the indicator balances. For a genuine constant-amplitude pure cohort the nonzero common amplitude can be canceled in the coefficient field, and the indicator balances do follow.

In particular, **outgoing transfer and direct cohort output are one order apart**. If the *original* \(\boldsymbol\Phi_t(A)|_D\) is constant on \(D\) for all \(|t|\le p-1\) and \(B\mathbf1_D=0\), principal deletion provably cannot change any retained tree vector through size \(p\). A discrepancy first seen on \(D\) at size \(p\) can spoil final order \(p\) by its direct cohort output, but cannot first spoil order \(p\) by transfer to a retained receiver. A transfer-only failure at order \(p\) needs a visible cohort discrepancy by tree size \(p-1\), or failure of the stated indicator balance. This is an exact implication about the rooted size, not a heuristic about a presumed chronological delay.

## Same clock is insufficient, even for a genuinely coupled strict SDIRK cohort

A balanced cohort at a common clock only makes \(\Delta_i\mathbf1_R=0\), i.e. the size-one input test. Here is a simple rational strict SDIRK example with true internal coupling, no normalization or asymptotic issue:
\[
 A=\begin{pmatrix}
 1/3&0&0&0&0\\
 2/3&1/3&0&0&0\\
 1&0&1/3&0&0\\
 0&1&0&1/3&0\\
 1&0&1/2&-1/2&1/3
 \end{pmatrix},
 \qquad
 \mathbf b=(3/4,1/4,1/24,-1/12,1/24).
\]
Take \(R=\{1,2\}\) and \(D=\{3,4,5\}\). The three deleted clocks are \(4/3\), \(A\mathbf1_D=\mathbf1_D/3\), and their output weights sum to zero. Hence every linear word \(bW(A,C)\) kills \(\mathbf1_D\), even though the fifth row has actual nonzero incoming entries from the third and fourth rows. The clock vector is \((1/3,1,4/3,4/3,4/3)\) and
\[
 A\mathbf c=(1/9,5/9,7/9,13/9,7/9).
\]
The retained weights already give \(b\cdot1=1\), \(b\cdot c=1/2\), \(b\cdot c^{\odot2}=1/3\) for the full method, while their tall-tree read is \(2/9\). The cohort contributes \((7/9-13/9)/12=-1/18\) to that read, so the full method has order three. Its bush of size four has read \(5/18\ne1/4\), so order three is exact. The principal retained method still has order two but not three. The retained columns are unchanged at *every* size since \(B=0\) in this example: the failure is entirely at the output. The example shows why even a true invisible linear eigenline and equal stage clocks, without the incoming annihilator at the needed rooted size, do not justify deletion.

## What this buys for lower bounds, and a strictly local measurable hypothesis

For each contrast \(\Delta_i\), lower triangularity makes its support lie on retained indices strictly before the physical row \(i\). Restricting the principal retained tableau to that literal prefix preserves all its tree weights there. Thus the test is against its actual prefix tree span, or the restriction of that span to the support of the contrast, not against an abstract count of donor labels. This can be substantially easier than checking a whole deleted-cohort tableau. For example, if the known lower-degree restricted span is already full on that support, or already equals its final needed restricted span, the paid partial agreement upgrades to the full annihilator. Full rank is not needed: verifying closure of the actual prefix space under \(\widehat A\) and coordinatewise products also gives true stabilization. A single flat rank step alone does not certify closure under all products. A particularly simple sufficient instance is that the actual contrast is supported on a sufficiently small number of retained rows with pairwise distinct clocks: the known bushy powers on those rows then span by Vandermonde. Repeated clocks require true profile/rank information, not just the pooled scalar moments.

The general algebraic test may be still weaker than requiring a common profile. For example, an actual subspace \(L\) on \(D\) which contains the unit, is closed under coordinatewise product and \(M\), contains \(V U_{p-1}\), and lies in \(\ker B\cap\ker\mathbf b_D\), makes all requisite \(z_t\) invisible. One can also use the exact finite test without assuming such a closed space. Under pure one-line information, the aggregate-top contrast test above is the weakest exact conclusion once all lower cohorts agree; it does not require \(\Delta_i\) on the last grade independently.

A least-stage DIRK/SDIRK at order \(p\) cannot have a cohort satisfying this deletion test, since the retained method stays in the same class at the same order. In particular, a balanced undeletable cohort must exhibit a true retained-profile contrast by size \(p-2\), or a nonzero aggregate top read on size \(p-1\), if all lower individual contrasts vanish. This is an actionable common postprocessing and lower-bound criterion when a rank argument can supply stabilization or the relevant row annihilator. It does not by itself prove that **every** candidate at an established stage floor has such a cohort.

In the previously audited dirty-first frame every genuine singleton omitted cohort is already deletable. For the repeated cohort the paid two-live-row agreement through size \(m+2\) at \(p=2m\) gives only contrast annihilation through size \(m+1\) (unless extra actual support rank is measured). It does not reach size \(p-1=2m-1\); even with no retained feedback the weighted top obligation remains for opposite nonzero weights. Thus the conditional simplification transfers to ERK, DIRK and strict SDIRK without any stronger published stage bound, and it identifies the exact missing witness rather than claiming that repeated clocks or linear output invisibility are sufficient.
