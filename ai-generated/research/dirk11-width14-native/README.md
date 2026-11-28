# Reviewed native exact order-eleven DIRK in fourteen real stages

This proof certifies the identical [literal real-algebraic construction](../dirk11-width14-real-reflected-shell/README.md) using the reviewed rooted-tree order predicate in Lean. It does not improve the **13–14** real stage interval or assert that those coefficients are rational.

- `RKResearch.Certified.DIRKOrderElevenFourteenReal.exact_of_roots` takes four roots of the displayed coefficient relations in any characteristic-zero field, and proves the literal tableau is lower triangular, has `HasOrder 11`, and does not have `HasOrder 12`.
- `RKResearch.Certified.DIRKOrderElevenFourteenReal.exists_exact_real` proves an exact 14-stage real witness.
- The finite-domain and independent full rooted-tree replays are separate results. The kernel proof does not assume any Python enumeration is complete or any exact rank solve returned a correct answer.

## Integral tower and graded replay

The [frozen coefficient JSON](../dirk11-width14-real-reflected-shell/tableau.json) is in a tower of four monic quadratics. The integer native data scales its generators by \(1,33,33,82693911948500160\), respectively, to clear the monic reductions. Table entries and weights are integral tower elements divided by one common positive integer denominator; the denominator has 57 decimal digits. The first three scaled roots are positive square roots. All eight coefficients of the numerical constant part of the fourth reduction are strictly positive in those positive roots. Thus the fourth equation \(w^2=d_0+d_1 w\) has positive discriminant \(d_1^2+4d_0\) and a unique positive root. This gives a real place without approximating or assuming any signs of the tableau entries. The same construction, being a tower of four algebraic radicals over the rationals, is real-algebraic; the native existential theorem is stated over \(\mathbb R\).

The checked grade spans have dimensions \(0,0,0,1,2,3,5,8,11,12,13\). The last three are allowed moment-null superspaces, not claims of exact actual grade ranks. Each closure witness has just one positive integer clearing scale, and the exact coordinate check uses no rational gcds. The literal stage action, clock action, componentwise products, monomial primitive corrections, scalar moments and output silence are proved by ordinary kernel arithmetic. A power cache has separately checked base and multiplication recurrence; the proof rewrites with its equalities before verifying high monomial reads. The [reviewed sufficient flag theorem](../../lean/RKCert/ReviewedNative/SufficientGradedFlags.lean) turns these finite certificates into the literal `HasOrder 11` result.

The separately checked order-12 failure tree has four leaf children and one seven-vertex bush at its root. Its scaled normalized residual is \(84\,b^\mathsf T[c^{\odot4}\odot A(c^{\odot6})]-1\). The proof multiplies its exact integral numerator by a stored inverse numerator and checks a nonzero literal integer. Its failure therefore persists in every characteristic-zero specialization satisfying the four relations, even if that realization is not an injective map from the unspecialized quotient.

## Rebuild

Python 3's standard library suffices to regenerate the table and proof jobs. From the repository root, with the frozen literal unchanged:

    python3 -B ai-generated/research/dirk11-width14-native/build-flags.py
    python3 -B ai-generated/research/dirk11-width14-native/build-checks.py

The generated powers, matrix entries, and coefficient witnesses are checked by Lean; the scripts are not trusted by the proof. With the pinned Mathlib dependencies available, from `ai-generated/lean` use:

    lake build +RKCert.ReviewedNative.DIRKOrderElevenFourteenReal:olean
    lake env lean AuditReviewedNativeDIRKOrderElevenFourteenReal.lean

On a memory-constrained machine, prefer one sequential compiler worker. Once the pre-existing repository and Mathlib imports are built, the [source list](lean-modules.txt) gives the topological build order relative to the repository root. For example, from `ai-generated/lean`:

    mkdir -p .lake/build/lib/lean/RKCert/ReviewedNative
    while IFS= read -r path; do
      file=$(printf '%s' "$path" | cut -d/ -f3-)
      case "$file" in Audit*) continue;; esac
      stem=$(printf '%s' "$file" | sed 's/[.]lean$//')
      lake env lean -o ".lake/build/lib/lean/$stem.olean" "$file" || exit
    done < ../research/dirk11-width14-native/lean-modules.txt
    lake env lean AuditReviewedNativeDIRKOrderElevenFourteenReal.lean

The [typed audit](lean-audit.txt) is the full native build's axiom check.
The [separate four-version arithmetic check](arithmetic-versions.log) compiles the unchanged raw definitions and five representative kernel decisions in Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 without Mathlib; it is not a claim of four full Mathlib builds. To generate that standalone check:

    python3 -B ai-generated/research/dirk11-width14-native/arithmetic-compat.py /tmp/DIRK11Arithmetic.lean
    lean /tmp/DIRK11Arithmetic.lean
