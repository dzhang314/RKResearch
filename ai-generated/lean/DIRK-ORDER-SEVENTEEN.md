# All fields of characteristic zero: order 17 needs at least 24 DIRK stages

**Final Lean declarations.** `RKCert.Paired.dirk_order17_twenty_four_charZero_field` and `RKCert.dirk_order17_twenty_four_charZero_ring`. Input is the original coefficient array, lower triangularity, all rooted-tree order equations through (p), and (17≤p); conclusion (24≤s). No ordering, realness, algebraic-closure, nonzero output, stiff accuracy, or stage-merger assumption. This includes the complex field and arbitrary characteristic-zero commutative rings, including those with zero divisors. No positive-characteristic claim.

## What removes the former square-root exception

Suppose 23 actual rows reach order 17. The field-independent existing theorem eliminates the non-C(2) branch. In the remaining anchored branch, the existing early marked-surplus theorem applies unless the grade-five marked dimension is at most three. On this minimal chart:
1. Any original cubic defect is jointly invisible to both the output and the reverse cubic: two actual paid ports give four and three primitive observations; the universal quintic 4+3 gate applies. Thus the jointly invisible space has dimension at least one. The sharp signed cubic physical count uses at least 15 of the 23 rows; at most seven distinct clean, output-active clocks remain. Zero is among them at the true terminal. These are actual row counts, not a reduction to fewer stages.
2. If both (v,Cv) lie in (F₅), then the first reverse clock is already paid. On at least seven distinct cubic clocks the two fitted polynomials satisfy (R=XQ), hence the original test polynomial (Q) has degree at most four. A true grade-five trace has profile (XQ) and support only on the clean clocks, and supplies a 3+2 pair of tests at two distinct, nonzero clean clocks (u,v). Let (T) be the monic nodal product on the clean clocks other than (0,u,v); its degree is at most four. For (k=0,…,5), pair the grade-five trace with (X^k(X-u)(X-v)T), of degree at most eleven: (5+11+1=17). The actual row pairing is zero pointwise, so all six ordinary formal moments of (X^{k+1}(X-u)(X-v)QT) vanish.
3. If (Q≠0), its two physical tests force (a=v/u) to satisfy (15a²-24a+10=0). They also determine (Q) up to nonzero scale. With (t=15a), its two-pivot multiple has the shape (d\, \mathrm{body}(t,u)), where (d≠0) and (t²-24t+150=0). This is a proved polynomial identity, not a numerical matching ansatz. Let (h_n=12252240\int_0^1 x^{n+1}\mathrm{body}(t,u)(x)\,dx), for (n=0,…,9); the common denominator is the LCM of 2 through 17. The five coefficients of (T≠0) are killed by each 5×5 Hankel matrix (h_{k+i+j}), (k=0,1). Therefore both determinants vanish at (u), so their padded degree-30 resultant is zero.
4. The resultant is an integer polynomial in the **single fixed integral parameter** (t). Modulo 1009 the marked quadratic splits at the two simple roots 135 and 898. At each, the two degree-30 minor polynomials are coprime, proved by explicit Bézout witnesses. Each of the four polynomials is reconstructed by 31 distinct evaluations with small exact LDLᵀ certificates: 124 checked determinants in total. Mathlib integral closure/lying-over transports nonvanishing of this fixed resultant to any characteristic-zero field. No specialization of the unknown physical pivot (u), the nodal factor (T), or tableau coefficients is used.
5. Consequently every synchronous (F₅) defect is jointly invisible, including all (F₄). The actual forward rank band now contradicts visibility, using the independently proved original-array fifth-debut obstruction for a length-one head. This closes the minimal case over all characteristic-zero fields. Finally the existing characteristic-zero ring-to-field specialization preserves the full original stage count.

The source's formal moment is the characteristic-zero linear polynomial primitive evaluated at one; no analytic integral, sign, or positivity enters this proof. `replay_dirk_order17.py` independently checks the fixed finite arithmetic using only Python's standard library; the public Lean declarations do **not** assume that program's results.

## Reproduction

Use the pinned Lean and Mathlib v4.36.0:

```sh
lake build RKCert.DirkOrder17FullCharZero
lake env lean AuditDirk17CharZero.lean
lake env leanchecker RKCert.DirkOrder17FullCharZero
```
