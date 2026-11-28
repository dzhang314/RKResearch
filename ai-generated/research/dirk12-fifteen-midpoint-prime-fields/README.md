# Optimal DIRK order twelve over prime fields and their prime-power rings

Fifteen stages are necessary and sufficient for ordinary DIRK of exact order twelve over the prime fields of orders **131 and 149**, their 131-adic and 149-adic rings and fields, and all nonzero commutative algebras over these rings or over their prime-power quotients. In particular no coefficient extension of the prime field or the prime-power ring is required. The lower bound is the [paid arbitrary-ring stage floor](../../lower-bounds/paid-beta/DIRK-PAID-GRADE-SIX.md). This is not a strict SDIRK construction and does not show that the rational upper bound is fifteen.

## Literal witnesses and lift

The eight JSON files are literal lower-triangular \(15\times15\) tableaux; all have an explicit first and last row and exactly four zero weights. An independent standard-library replay checks each full tableau against all **7,813** rooted conditions through order twelve and the scaled order-thirteen bush \(13\sum_i b_i c_i^{12}-1\). Its value is nonzero in every listed field. For example:

| Prime | \(x\) | \(f\) | \(d\) | Scaled order-13 bush | Successive derivative residues |
|---:|---:|---:|---:|---:|---:|
| 131 | 111 | 57 | 85 | 20 | 109, 53, 16 |
| 149 | 103 | 41 | 106 | 118 | 12, 139, 96 |

The literals come from the same exact formulas as the [real algebraic construction](../dirk12-fifteen-midpoint-real-upper/README.md), with \(a=1/2\). For each row of the table above the three successive equations are the degree-36 polynomial for \(x\), the monic cubic for \(f\) after recovering \(y,t\), and the orientation quadratic \(d^2-sd+p=0\), where \(p\) in this quadratic is a scalar product, not the residue characteristic. The lift replay checks the actual roots, derivatives, all constructor denominators (which are units), and literal coefficient equality at each residue. The nonzero derivatives give successive Hensel lifts with the selected residues, and these define an embedding of the characteristic-zero coefficient field into the corresponding \(p\)-adic field. The exact rooted identities therefore hold in that field and, as the lifted entries are integral, in its ring of integers. Reduce and base change to obtain the quotient-ring and algebra results. The next-order defect reduces to a nonzero element and is a unit throughout. In particular the same optimum holds over every nonzero commutative ring in which either 131 or 149 is nilpotent, and by the Chinese remainder theorem whenever \(131\cdot149\) is nilpotent.

Run **python3 -B all-rooted.py** for the eight complete literal replays and **python3 -B lift-replay.py** for a full literal-rooted check at exponents 1, 2, 3, 8, and 20 for one representative of each prime. The proof covers every exponent, not only the tested samples. The whole construction and base change above are mathematical; no new native Lean tableau theorem is claimed.

## Coefficient recovery and the second real tableau

In one-based physical numbering the real literal's row sums recover its defining generators:
\[
       x=2c_7,\qquad f=c_{10},\qquad d=1-c_{12}=1-c_{14}.
\]
All entries are in \(K=\mathbb Q(x,f,d)\); the recovery proves \(\mathbb Q(A,\mathbf b)=K\). Thus the degree **216** in the [field receipt](../dirk12-fifteen-midpoint-degree216-field/README.md) is the exact degree of the tableau coefficients. It is not merely the degree of a convenient ambient field. All 216 embeddings into \(\mathbb C\) give distinct exact tableaux because the generators are recovered from the entries, and every embedding preserves all rooted identities and the next-order failure. In the isolated real \((x,f)\) embedding the quadratic involution exchanges \(d\) and \(v\). Its conjugate is a second exact real tableau with a different repeated nonzero-weight clock; the multiset of nonzero-weight clocks shows that the two cannot be identified by a simultaneous permutation of physical stages. This proves at least two real embeddings giving distinct tableaux, without counting all real embeddings of \(K\).

More generally, in the two **specified** midpoint chronologies of the [projection](../dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection/README.md) and [split-free reconstruction](../dirk12-fifteen-rank3-invisible-split-free-grid/README.md), the same irreducible equations successively constrain actual clock coordinates. The degree-20 alternative was excluded in that projection. The remaining degree-36 polynomial, the monic cubic and the orientation quadratic are irreducible at each successive field step. Thus every candidate meeting those hypotheses contains a subfield isomorphic to \(K\); if its coefficient field is a number field, its degree is divisible by 216. The nine-site construction attains 216. This excludes rational coefficients only in the stated midpoint branch, not in other order-twelve 15-stage charts.

## Prime-field coverage of this fixed algebraic witness

Discard finitely many bad primes: those dividing a denominator or the norm of the scaled next-order defect, the ramified primes of the normal closure, and the finite conductor primes at which the localized coefficient order is not the full ring of integers. A residue field of \(K\) above any remaining prime gives an exact 15-stage method of order twelve. Reduction to the prime field itself is equivalent to a degree-one place: at good primes the three generators are integral, and the field is recovered from the actual coefficient entries. By Chebotarev the density of these primes is the fraction of the normal-closure Galois group whose permutation on the 216 embeddings has a fixed point. The action is transitive, so the mean number of fixed points is one. Each permutation having any fixes at most 216; hence this fixed tableau alone gives prime-field coverage of natural density at least \(1/216\). This is a lower bound for unrestricted prime-field coverage, not an equality or a count of all methods.

For contrast, at 137 the degree-36 polynomial for \(x\) remains irreducible with unit leading coefficient. Any integral specialization of this tableau must therefore have residue degree divisible by 36, since \(x=2c_7\) reduces as an actual coordinate. This neither proves a method at 137 nor rules out a different tableau over the prime field there.
