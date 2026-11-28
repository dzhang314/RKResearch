# Sixteen-stage exact ERK10 in five further prime families

For each \(p\in\{29,37,41,43,59\}\), there is a compatible
sixteen-stage explicit tableau of exact order ten over every
\(\mathbb Z/p^n\), and hence over \(\mathbb Z_p\) and \(\mathbb Q_p\).
It transfers to any nontrivial commutative ring in which \(p\) is
nilpotent. The normalized eleventh-bush discrepancy is a unit.
The five families can also be combined by integer CRT with one another
or with the [earlier prime-power families](../erk10-sixteen-expanded-prime-portfolio/README.md).
This is a coefficient-domain upper bound. It makes no rational or
unrestricted claim.

| Prime | Horizon | Raw reverse clocks modulo \(p\) | Unit eleventh-bush defect |
| ---: | ---: | --- | ---: |
| 29 | 15 | \(1,0,6,14,16,4,22,26,25\) | 24 |
| 37 | 5 | \(1,0,25,35,9,12,20,31,3\) | 16 |
| 41 | 16 | \(1,0,20,18,27,8,36,37,23\) | 13 |
| 43 | 18 | \(1,0,16,11,19,8,22,40,13\) | 14 |
| 59 | 7 | \(1,0,33,53,47,9,5,42,26\) | 41 |

## The guarded lift

Use the [late-helper construction](../erk10-late-helper/README.md).
Take the doubled-clock eight-stage dense prefix at the stated *rational*
horizon and hold its coefficients fixed throughout the lift. The exact
prefix builder uses all 17 ordinary identities through grade five
to check the dense decoder, the literal final-row identity, and
the three-dimensional span of the grade-six source polynomials.
Every size-six source is eliminated against the same three paid basis
rows, not just checked at the residue prime. All numerator-denominator
coordinates of the prefix, decoder and source basis are integral at
the selected prime.

Keep the late sites \(d,e,\xi\) fixed at the displayed integers.
Use the normalized terminal quadratic \(F(z)=C_0\Delta+C_1N_S+C_2N_P\)
of the accompanying recipe, with \(z\) the remaining weighted donor
at reverse index five, starting at its table entry. The residue
Jacobian and pair guards are:

| \(p\) | \(F'(z)\) | \(\Delta\) | \(S^2-4P\) | root derivatives \(2a-S,\ 2b-S\) | helper denominator |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 29 | 22 | 15 | 6 | 21,8 | 23 |
| 37 | 32 | 12 | 26 | 27,10 | 35 |
| 41 | 9 | 32 | 4 | 2,39 | 9 |
| 43 | 18 | 20 | 25 | 5,38 | 41 |
| 59 | 47 | 23 | 46 | 39,20 | 48 |

Lift \(z\) uniquely by the one-variable Hensel step. If a root has
been paid modulo \(p^r\), the increment \(p^r u\) changes the
normalized residual modulo \(p^{r+1}\) by \(p^r uF'(z)\);
the derivative is a unit by the table. Then form the exact monic early
pair using \(S=N_S/\Delta,\ P=N_P/\Delta\). The two branches of
\(u^2-Su+P\) lift independently from the residues \(a,b\) because
both derivatives are units. Their sum and product are \(S,P\):
subtract the two root identities and use the unit \(a-b\).
The two nodal orthogonality equations make the eight-site cardinal
rule integrate through degree nine. All site gaps, the required
cardinal masses and the linear helper solve are units.

The four base reverse reads use the same initial donors, with the
first-read residual checks at the actual first and second weighted
sites. The degree-four and degree-five terminal tests annihilating
the late adjustment rows have at least one unit value of \(\ell\):
if both were zero modulo \(p\), the whole terminal quadratic would
be zero there, contradicting the nonzero derivative. Hence \(F=0\)
on the lifted pair makes the cubic base read proportional to \(\ell\)
on those tests. Evaluation at \(d,e\) is onto from the full source
polynomial ambient space (use the distinct unit gaps); its kernel
is exactly the span of those two tests. Independent compensated taps
to \(z\) therefore pay the cubic read on the size-six source space.
The three cofactor payments then solve independently using the
zero-weight helper. Their determinant is a unit, verified by the
listed pivot replay. All numerical solves at larger exponents use
the same residue guards. The marked-source construction and literal
one-stage merge now give \(8+9-1=16\) stages and HasOrder ten.
The next bush remains nonzero because its displayed residue does.

This argument supplies all powers, not just the three frozen
literal exponents. It uses ordinary polynomial Hensel lifting over
integer prime powers. The marked-source derivation and all-power
argument are mathematical proofs with exact replay, not asserted as
an end-to-end native Lean lift here.

## Replay

    python3 -B verify.py
    python3 -B build.py --exponent 3 --emit /tmp/erk10-late-helper-lifts
    python3 -B verify.py /tmp/erk10-late-helper-lifts
    (cd /tmp/erk10-late-helper-lifts && sha256sum -c "$OLDPWD/literal-sha256.txt")
    sha256sum -c source-sha256.txt

The independent verifier enumerates ordinary child multisets using
integer partitions, without importing the builder. It checks all
1,205 rooted conditions, the unit eleventh bush, and compatible
reduction of the entire matrix, weights and raw clocks. The three
frozen powers include **15** independently verified literal tableaux.
