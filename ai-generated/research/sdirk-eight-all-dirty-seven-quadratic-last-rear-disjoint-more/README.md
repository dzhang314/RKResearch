# Five more non-overlapping one-extra rear D charts

Keep the [scoped single-end hypotheses and three-label recovery](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-two-star/README.md): ordinary order at least eight, strict ten-stage SDIRK over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven distinct clocks, exactly one singleton physical endpoint, and two genuine oriented three-stage prefixes using **disjoint** doubled labels. The forward opening has two singleton labels and the backward opening has two doubled labels. This packet excludes five additional pairs of genuine phases, using the general three-singleton and two-D equations in that companion. These complete all cases except forward A2 / rear A2 and forward A2 / rear A3 within this topology. The terminal and extra-rear overlaps were excluded in their own packets.

The arithmetic phase names refer to whether the **non-initial doubled label** is second (A2) or third (A3), not a tableau reordering. For the star, both orders give the same exact measured non-initial pair data because the physical star edges satisfy equal residuals; no statement about arbitrary row permutations is made. The third recovered doubled clock is the actual nonterminal rear doubled label. Its measured defect and that at the true terminal row both contribute. Neither the unknown next singleton nor any freely chosen partner at a doubled clock is needed.

## Projections and exact guard census

Denominators and all removals are those in the [non-overlap ingress](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-two-star/README.md#one-unknown-d-clock-recovered-by-pure-affine-interpolation). For arithmetic reversals use the general \(k=e,H\) scaled equations before the rear-star simplification. In a characteristic-zero field any true \(H\) is a root of the gcd of the two projected integer rows (after stripping only their true \(H\)-guards). The exact profiles are:

| Front / rear | Projected degrees | \(H\)-factors with multiplicities |
| --- | --- | --- |
| A2 / star | 955,1185 | (4,2) three times,(36,2),(2,3),(3,8),(12,8),(18,8),(27,8) |
| A3 / A2 | 928,1018 | (18,2),(4,8) twice,(2,9),(4,9),(18,20) |
| A3 / A3 | 925,555 | (12,1),(18,2),(4,3) twice,(2,3),(4,4),(18,10) |
| star / A2 | 829,919 | (6,6),(4,16),(1,18),(2,18),(9,40) |
| star / A3 | 829,459 | (1,6),(4,6),(6,6),(2,6),(9,20) |

The \(H^2\) coefficient identifies quartics sharing the same degree and multiplicity. For each factor, the table fixes a simple full-degree good place and the exact pre/post degrees of a monic anchor after removing factors of true guard polynomials: some literal clock differences, \(L_4(d)\), actual paid tap numerators or both affine slope zeros. These trims take place in the abstract \(H\)-field before specialization and preserve every actual \(d\). For the quadratic fibres the actual raw rows are used with at least one positive exact degree preserved. Every quotient-row model has a joint unit gcd at its stated place. This tests the whole residue algebraic closure, not just roots in its prime field. It is a proof for all characteristic-zero fields, not a field-order/sign deduction or a claim about the chosen finite characteristics.

## Exact primitive resultant, optional individual replay

For the A2 / rear-star pair, an independent replay uses two resultants via a primitive polynomial remainder recurrence over \(\mathbb Z[H]\). For one division \(A\) by \(B\) in \(d\), each recorded primitive step has the form
\[
 C_{\mathrm{next}}=(y C_{\mathrm{previous}}-x d^j B)/c,
\]
where \(c\) is the exact nonzero content removed, with \(x,y\) taken from the leading monomials so that the actual \(d\)-degree decreases. At any root of \(B\), these steps multiply the previous value by \(y/c\). If \(\deg_d A=m,\deg_d B=n,\deg_d C_{\mathrm{last}}=r\), the resultant products therefore give, up to sign,
\[
 \operatorname{Res}(A,B)=
 (\operatorname{lc}_d B)^{m-r}
 \left(\prod c/y\right)^n
 \operatorname{Res}(B,C_{\mathrm{last}}).
\]
The terminal constant yields its usual degree power. The verifier tracks exact numerator and denominator polynomial valuations, cancels every negative valuation and forms the ordinary resultant up to a nonzero rational scalar. It also checks the ratio to direct univariate integer resultants at three full-degree integer specializations. This handles actual degree drops automatically after specialization, without dividing by a candidate-valued leading coefficient. The default A2 projection uses the separately proved [deterministic bounded-height CRT](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-final/README.md#deterministic-exact-reconstruction-not-a-modular-search), and the smaller rows use ordinary exact FLINT multivariate resultants. The runner uses the lower-memory canonical fraction engine for the unchanged physical equations.

Run `SYMPY_GROUND_TYPES=flint python check_more_disjoint.py` (SymPy 1.14 and python-flint 0.8); append ID(s) such as `S-A3` or `A2-S A3-A2` to replay only those pairs. Use `--primitive-a2` for the independent recurrence on A2/star, or `--fast-library /path/to/lib.so` with the optional compiled kernel only for the CRT method. On a memory-limited system, use five separate invocations: `A2-S`, `A3-A2`, `A3-A3`, `S-A2`, `S-A3`. Separate processes release temporary polynomial storage between branches. The tables cover 32 fibres. The [candidate Lean scalar clearing lemmas](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDisjointRearStar.lean) are shared with the non-overlap companion; the actual tableau proof and exact elimination are paper/exact Python, not all native Lean. The general stage interval is unchanged.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
