# Nine strict SDIRK stages over finite 19-primary rings

A [different, quadratic tableau](../strict-sdirk7-quadratic/README.md) extends the exact nine-stage result to all positive powers of 19. The finite lifts documented here are kept as independent arithmetic and Lean witnesses.

The previously found nine-stage exact order-seven tableau over F19 lifts
to Z/(19^12), and thus to each Z/(19^k) for 1 ≤ k ≤ 12. The first thickening
already has diagonal 293 and eighth-bush payment 278 modulo 361. At the top
modulus, 2,213,314,919,066,161, the diagonal is 1,310,024,100,145,885 and
the eighth-bush payment is 1,281,827,714,603,969. Both the diagonal and the
difference of the bush payment from one are units at every level.

The literal Lean certificate
`RKCert.Research.SDIRKNineStageOrderSeven19Powers` checks both endpoint
tableaux modulo 19² and 19¹² through the reviewed `HasOrder` predicate.
It also proves the stronger base-change statement: nine stages suffice
for exact order seven over every nonzero commutative ring in which
19¹²=0. If a coefficient ring in this family admits a unital map to F19,
the independent F19 exclusion gives nine as the minimum. This includes
Z/(19^k) for the full proven range, but not necessarily other coefficient
rings of the same characteristic, since a map *from* F19 to an extension
field is not the required map *to* F19.

The construction is exact and digit-wise. Write the 85 factorial-scaled
order conditions as integer polynomials in 46 unknowns: one common
diagonal, 36 subdiagonal entries, and nine weights. At the original
residual solution, their Jacobian modulo 19 has rank 43. For an exact
solution modulo 19^k, expanding at a correction of size 19^k gives the
same residual Jacobian times the new digit; terms quadratic in the
correction vanish modulo 19^(k+1). Each system here is consistent and we
take the free digits to be zero. Rank 43 alone does not guarantee that
the next digit will exist. We claim only the fixed prefix through 19^12,
not a 19-adic, rational, or factorial-localized lift.

- `nine-stage-19-power-lifts.json` records the residue, the first
  thickening, and the highest tableau.
- `python3 construct-lifts.py` recomputes the Jacobian, checks each of
  its columns against full finite differences, and rebuilds all 11
  lifts by row reduction.
- `python3 check-lifts.py` is independent of this procedure. For all
  twelve reductions of the literal top tableau it enumerates trees by
  integer partitions, verifies all 85 order conditions, and checks the
  unit eighth-order defect and unit diagonal.
