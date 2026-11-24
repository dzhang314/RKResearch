# ERK order nine: five-off/six-on good-prime exclusion

These ten additive Lean modules finish the eight-factor check of the exact
characteristic-zero scalar H48 atlas at the prime 1319. The six earlier
checked rows (factor degrees 2, 3, 4, 6, 7, 7) are reused unchanged.
Only the two remaining rows (degrees 9 and 10), and the degree-48 factor
multiplication, use the new compact arithmetic.

## Checked statements

Import `RKCert.ERKOrderNineCompactPrime`.

- `RKCert.CompactResidue.sixOn_atlas_impossible`: in any characteristic-zero
  field, three distinct roots of the Lobatto pencil satisfying the actual
  `sixOnK8` condition cannot make `sixOnTerminalProduct` zero.
- `RKCert.Paired.order9_no_five_off_six_on`: a strict 12-stage order-nine
  explicit tableau over an ordered field cannot have five off and six on nodes.
- `RKCert.Paired.order9_only_one_off`: with the earlier physical census, such
  a hypothetical tableau has exactly one distinct off node. **The one-off
  atlas is not excluded here; this does not prove a 13-stage lower bound.**

## Verifier interface and invariants

`ERKCompactResidueCore` imports only the Lean prelude.
`ERKCompactResidueSound` proves the coefficient and evaluation semantics.
Lists hold natural coefficients in ascending degree order and are zero
outside their length; no canonical representatives, nonnegative degree
claims or trimming assumptions are needed. An arithmetic record consists
of its two incoming values (one for negation), its output `C`, and, for
multiplication, a quotient `Q`. With `n = R.length`, where `R` is the
negated lower-coefficient list of the monic factor, the verifier checks

    AB + RQ = C + X^n Q       coefficientwise modulo p.

It checks degrees below max(len A + len B, len C, len R + len Q).
Above that cutoff all four terms have zero coefficient. This is a
formal polynomial equality over any commutative ring of characteristic p
(`mul_polynomial_relation`). At a root of X^n−R, the identical Q terms cancel
(`mul_witness`). For unreduced multiplication use `r = q = []`
(`mul_polynomial_witness`); `Product.correct` chains these witnesses.
Add and negation check the corresponding coefficient sums. `Value.correct`
extends the result to ring expressions and `SameValues.correct` compares
coefficient arrays entry by entry.

Each local Boolean identity uses ordinary kernel conversion,
`of_decide_eq_true rfl`. The row-adapter theorems separately check that the
resulting syntax is definitionally the exact existing split, diagnostic,
and terminal recipe. No factorization, interpolation, numerical search,
Python output, or external calculation is assumed. The named arithmetic
nodes share earlier proofs. No `native_decide`, placeholder or new axiom
is used. The two Python generators and their input data are optional
provenance; their output encodes what the kernel verifies, not a trusted
checker. The original six small rows still use their earlier
proof-producing `cbv` tactic and are not rebuilt by this delta.

## Exact dependencies and receipt

Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`;
Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The base is the
sealed physical p9 chart on project baseline `1e545bba`, together with:

- `rk-erk-order9-good-prime-support-20261124.zip` SHA-256
  `f2f9b72cf888f1e20cd2a3c86ff27e089907249312db2c85469bfeac916f0ecc`.
- `rk-erk-order9-good-prime-rows0to5-20261124.zip` SHA-256
  `b7ba063e2728f721244245983897c923ec402549525104753d530dd3eef6a526`.

The direct shared boundary files are listed in `BASE_IMPORTS.sha256`.
Place the additive source files in the project's usual `RKCert` build
root after integrating these prerequisites. The final module imports
each checked source dependency; no compiled object is shipped.
`Axioms.lean` and receipts give the measured proof/replay results.

The compact degree-9 tape took 40.994s and used 1,403,472 bytes for its
private .olean; degree 10 took 61.109s and 1,430,896 bytes respectively
(the worst compact row). The two recipe links took 6.049s and 7.151s.
The separate H48 formal polynomial product took 7.742s, and the final
leaf 1.404s. Timings are wall-clock in the isolated pinned workspace,
not a bound for other systems.

The new core relies on core List/Nat/Bool reduction with
`of_decide_eq_true`, not a version-dependent reflection tactic.
Mathlib adapter APIs include `Polynomial.coeff_ofCoeffList`,
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ`,
`Polynomial.coeff_X_pow_mul'` and `CharP.cast_eq_mod`. The
`module` / `public import` / `@[expose] public section` exports are
fixed at the pin. Compatibility with earlier Lean/Mathlib versions has
not been tested in this receipt.
