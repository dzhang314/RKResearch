# Reviewed-native strict SDIRK(9,7)

The two public theorems in `RKResearch.Certified` exhibit a lower triangular
nine-stage tableau with one nonzero diagonal and classical order at least
seven over `ℝ` and over the actual relative algebraic closure of `ℚ` in `ℝ`:

- `strictSDIRK_order_seven_nine_stages_real`
- `strictSDIRK_order_seven_nine_stages_realAlgebraic`

`SDIRKNineReplay.order_seven` works over any characteristic-zero field
containing a nonzero inner parameter and a solution of the two certified
polynomial relations. For the archived witness, the inner coordinate is
`t = 4 z`, the outer coordinate is the smaller quadratic node scaled by
`shapeDen`, and the common diagonal is `4 / t`. The certificate proves
native `HasOrder ... 7`, not a translated tree or tableau predicate.
This source delta does not formally exclude eight stages or prove the
method's eighth-order failure. The earlier independent exact replay
does establish the latter arithmetically, outside the native Lean theorem.

## Arithmetic boundary

The enum contains all 197 reviewed binary constructors through order seven.
Its identification with the reviewed finite catalogue is proved in Lean,
and every shape is paid using the reviewed `Φ`. There are 57 stored reduced
stage vectors, 37 indexed matrix products, 19 indexed pointwise products,
and 85 distinct weighted checks. Alias proofs use the actual checked stage
vectors and pointwise multiplication, not numerical tree labels.

The integer radix is only a way to recover candidate polynomial quotients.
The kernel checks the integer packed equality and a proved coefficient
height bound; soundness holds independently of candidate recovery. Both
limbs of every quadratic numerator are interpreted at the exact root pair.
No native execution oracle, unchecked coefficient conversion, approximate
root selection, or human-code change is used. The two denominator units
cancel via the preexisting `FiniteScaledOrderCheck` theorem.

`compare-tableau.py` independently checks that the literal Lean data
represents the previously sealed tableau, including all 81 entries, all
nine weights, and the three normalized root polynomials. This is a
provenance check, not a Lean prerequisite. Invoke it with the path to
`SDIRKNineReplayData.lean` and the `tableau.json` from the named
parameter/archived-tableau seal in `result.json`.

## Replaying

Use Lean/Mathlib 4.36.0 as pinned in `result.json`. Set `LEAN_PATH` to an
isolated output root followed by the reviewed base's compiled library,
the five earlier additive dependency modules listed in `result.json`,
and the pinned Mathlib dependency libraries. Overlay only these new
source files under `ai-generated/lean`. From that directory, build the
listed source paths in `rebuild-order.txt` in order, running one
`lean -j1 -M 3000 -o "$out/${src%.lean}.olean" "$src"` at a time. Make
the output module directory first. Do not replace the reviewed modules.
Run `lean AuditReviewedSDIRKNineOrderSeven.lean` to check both consumers
and eight transitive axiom sets. The flagship compiled module was also
replayed using `leanchecker --verbose RKCert.ReviewedNative.SDIRKNineOrderSeven`.
The included compiler warnings are cosmetic optional-tactic/section
lints; the source is otherwise unchanged from the verified build.
