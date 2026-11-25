# Native exact order ten: assembly and independent replay

**Lean 4.36.0 accepted the complete certificate against the pinned dependencies.**
The reviewed theorem proves order ten and rules out order eleven for the
same rational 27-stage tableau with common nonzero diagonal `1/9`.
The four typed audits passed. Read [the exact final audit output](evidence/Upper.audit-output.txt)
or see [the source and dependency locks](release.json).
The independent full replay from a fresh checkout has not yet been run.

The 28 support modules and the four typed audits are readable directly
in the repository. The remaining 1,358 generated files are regular Lean
source in a deterministic archive, not compiled proof objects. Their
exact hashes are listed in [the selected source manifest](selected-providers.tsv)
and tied to the [completed compilation batches](evidence/checked-source-bindings.tsv).
The replay below expands the archive in a disposable checkout.

This is a rational upper witness, not a minimum or a stability claim.
The eleventh tall weight is
`5946972394780345710421384301593 / 224017752875470299449731184306688000000`,
not `1/11! = 1/39916800`.

## File layout, from the RKResearch repository root

| Public repository path | Contents |
| --- | --- |
| `ai-generated/lean/RKCert/ReviewedNative/` | The exact 28 supporting providers: unchanged Data; TallValues, TallSteps 02–11 and Tall; 15 actual shard/scaffold providers including the measured Shape. Do not include conditional `FixedExact`. |
| `ai-generated/lean/RKCert/ReviewedNative/P10AugmentedRender/` **and** `ai-generated/lean/RKCert/ReviewedNative/RationalStrictSDIRKTwentySevenStageTenUpper.lean` | Together the 1,358 rendered providers, at these paths after materialization. Include exactly one Upper, the one importing Data, Tall and concrete Positive. Never install the competing ordered-tree facade at this key. |
| `ai-generated/lean/AuditReviewedRationalStrictSDIRKTwentySevenStageTen{Data,Tall,Upper}.lean` | Three **unchanged** stock typed/no-output audits. The braces here denote three separate paths. |
| `ai-generated/lean/AuditReviewedRationalStrictSDIRKTwentySevenStageTenAugmentedPositive.lean` | Small supplementary two-example audit of actual receipts and the same-data concrete positive; no object is required, nor is this a project provider. |
| `ai-generated/lean/tools/render_augmented_wiring.py` | Portable, optional source generation for the 13 assembly/dispatch/positive modules. It is not a generator for the other 1,345 rendered providers or a mathematical checker. |
| `ai-generated/upper-bounds/rational/strict-sdirk-order-ten-27/native-lean/` | This guide, wiring profile, source guards, selected-provider and existing-provider tables, release record and named terminal evidence. If using compact source transport, also `rendered-sources.tar.gz`. |

This release uses the compact source form. It changes no reviewed definition
and does not add the large certificate to the repository's default imports.
The Data, Tall, Positive and Upper audit outputs under `evidence/` are the
observed results from the pinned project build; they are not a cold replay.

## Independent replay commands

Use a new checkout / worktree, not the warm proof directory. Prepare all locked third-party packages using either independently verified published caches or a separately recorded clean build. For an offline run preprovision dependencies and block network access in the replay environment. Never use `lake update`; do not inject private library paths, `.olean` files or old project build directories. The nested package depends on the reviewed project at `../..`. Each `lake build +…` below invokes a **single named target** but Lake may schedule its dependencies; it is not a one-worker scheduling guarantee. An already active shared compiler must not be displaced by this run.

```sh
set -eu
cd "$(git rev-parse --show-toplevel)"
N=ai-generated/upper-bounds/rational/strict-sdirk-order-ten-27/native-lean
F="$N/selected-providers.tsv"
X="$N/existing-providers.tsv"
# Read values from the reviewed release record, never by hashing the input and trusting itself.
H=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["selected_providers_sha256"])' "$N/release.json")
BASE=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["preparation_base"])' "$N/release.json")
```

For the **capsule form only**, verify and materialize inside that disposable checkout; skip this if the sources are tracked normally. All archive contents are checked before any write, and symlinks, escapes, extra/missing/duplicate entries, unexpected member types, noncanonical headers and overwrites are rejected. On an interrupted filesystem write, discard the disposable checkout rather than overlaying partial files.

```sh
Z=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["capsule_sha256"])' "$N/release.json")
python3 -B "$N/capsule.py" materialize --repo . --manifest "$F" --manifest-sha256 "$H" \
  --bundle "$N/rendered-sources.tar.gz" --bundle-sha256 "$Z"
```

Then run the source checks and independent Lean gates:

```sh
python3 -B "$N/check_cut.py" --repo . --manifest "$F" --manifest-sha256 "$H" --existing "$X"
python3 -B ai-generated/lean/tools/render_augmented_wiring.py \
  --profile "$N/wiring-profile.json" --manifest "$F"
D=$(mktemp -d)
python3 -B "$N/audit_terminal.py" --repo . --manifest "$F" --manifest-sha256 "$H" \
  --existing "$X" --preparation-base "$BASE" --record-dir "$D/actual"
```

`check_cut.py` checks the exact source and package locks and import graph, not mathematical truth. The opt-in generator derives all ordered lower splits, all terminal splits, vector and leaf/scale fields, and the positive wiring from a small profile. The corrected Dispatch space is emitted in the template, not patched after compilation. It verifies all 13 generated source SHAs before writing anything; add `--emit "$D/new-wiring"` only to inspect an independent output tree. Reusing this generator for a different order requires the matching reviewed scaffold, independent selected source hashes and actual typed proof. No other order or new witness is certified here.

`audit_terminal.py` builds named Data, Tall, Positive and Upper **from `ai-generated/lean/`**, immediately executing each corresponding no-output audit with `lake env lean`. The audit scripts are passed as package-relative filenames, not a doubly prefixed `ai-generated/lean/...` path. The runner records each real child-process exit, combined raw log and SHA; source locks are rechecked after the build. It rejects pre-existing project build trees, foreign Lean path overrides and nonpinned dependency search roots. A new path layout or unexpected compiler message must be investigated, not filtered until it passes. These guards do not authenticate prebuilt third-party objects themselves: document the independent provenance or clean source build of Mathlib/dependency objects. Say “cold project replay with pinned dependency cache” if that is what was done.

## Exactly what the final checks establish

| Gate | Concrete typed declarations / output required |
| --- | --- |
| Data (stock, 3 reports) | `…Upper.actInt_eq`, `…Upper.outInt_eq`, `…Upper.shared_scale` on the unchanged witness. |
| Tall (stock, 2) | `…Upper.eleventh_tall_weight` with the exact displayed rational; `…Upper.not_order_eleven : ¬ HasOrder 11 A b`. Both are on the same Data. |
| Actual positive (supplementary, 2) | `RKResearch.Certified.P10AugmentedRender.literalReceipts : Receipts renderOps header lower`; `…P10AugmentedRender.checked_order_ten : RKResearch.HasOrder 10 …Upper.A …Upper.b`. No callers are asked to supply receipts. |
| Upper (stock, 4) | `…Upper.order_ten`, `…Upper.eleventh_tall_weight`, `…Upper.not_order_eleven` and `RKResearch.Certified.exists_twenty_seven_stage_rational_strictSDIRK_exact_ten`. The four unchanged typed examples require the positive, exact tall value, negative, and a single existential `∃ A b, A.IsLowerTriangular ∧ (∀ i, A i i = 1/9) ∧ (1/9 : ℚ) ≠ 0 ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b` at `Matrix (Fin 27) (Fin 27) ℚ` and `Fin 27 → ℚ`. |

Accept **each** #print report for the correct fully qualified name and only axiom subsets of `{propext, Classical.choice, Quot.sound}` (empty allowed). The runner requires all 3+2+2+4 reports in their own zero-exit audits. Unexpected axioms including `sorryAx`/compiler trust, partial output, an extra report, or an unexpected diagnostic stops acceptance. Do not claim eleven unique public theorems: two stock Tall names recur in the final four; the extra positive audit is not the stock final audit. The four already published generic audits and their eleven reports are a different evidence set.

The mathematical mechanism checks a real leaf, 95 actual scaled actions, 404 lower memberships (including the real homogeneous tail), 95 lower basis payments and 328 terminal scalar payments over the full ordered split domain. That explains the certificate, but the counts, an arithmetic checker, hashes, a prefix, or generic soundness **do not** by themselves imply the concrete final theorem. The independently released arithmetic table/checker and compact `augmented-span/basis.jsonl` are siblings of this directory, not native build inputs. Follow the independent commands in `../augmented-span/README.md` when reporting arithmetic evidence separately; do not copy their raw streams into the Lean release.

A successful independent replay records the exact checkout, selected source hashes, build and audit exits, and axiom reports. The evidence committed here is from the completed pinned project build.
