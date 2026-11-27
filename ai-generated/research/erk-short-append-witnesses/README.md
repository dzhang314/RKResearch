# Neither nearby rational stage bound is reached by a short append-only lift from these seeds

For each specific old tableau below, the entire numerical stage matrix is held fixed and new rows are appended strictly after it. The output weights are **free to change on all rows**. Exact old relations give:

| Fixed seed | Target order | At least this many new physical ERK rows |
|---|---:|---:|
| [11-stage dispersed rational ERK8](../erk-eight-dispersed/README.md) | 9 | 4 |
| [11-stage rank-three rational ERK8](../erk-eight-rank3-four/README.md) | 9 | 4 |
| [14-stage signed-triple rational ERK9](../erk9-fourteen-rational-triple/README.md) | 10 | 5 |
| [14-stage complementary rational ERK9](../erk9-fourteen-field-portfolio/README.md) | 10 | 5 |

This rules out merely appending two rows to these 11-stage seeds for rational ERK9 in 13, or appending one (or two, three, or four) to the listed 14-stage seeds for rational ERK10. It is **not** a lower bound on arbitrary rational extensions or new tableaux. The witnesses are valid over every characteristic-zero field containing the old coefficients. In the real-algebraic field the respective fixed-stage-matrix costs 4 and 5 are attained by the general [sharp extension theorem](../newton-tail-order-raising/SHARP-EXTENSION-COST.md); no matching rational append-only upper count is asserted.

## The reusable exact witness

Let \(\mathbf N_t\) be the normalized stage column with scalar model \(X^{|t|-1}\); its primitive satisfies \(\mathbf N_{[t]}=|t|A\mathbf N_t\). Each JSON file supplies integer coefficients of a linear combination of trees of size at most six. Its actual old column is zero, but its model \(f\) has \(\Omega=I(X^{d}f)\ne0\), with \(d=3\) for target order 9 and \(d=4\) for target order 10. The old asserted order \(p-1\) pays \(I(X^j f)=0\) for \(0\le j<d=p-6\).

In an extension with at most \(d\) appended explicit rows, applying \(A^d\) to that relation kills the entire stage column: the fixed old positions start zero and the new-to-new block is strictly triangular of width at most \(d\). But actual order \(p\) forces its weighted readout to be \(I(J^d f)\). Integration by parts gives \(I(J^d f)=I((1-X)^d f)/d!=(-1)^d\Omega/d!\ne0\). This is the specialized strict case of the linked general extension argument; no restrictions on the reoptimized weights enter.

## Verification

The Python finder derives the primitive integer relations by exact elimination and rechecks each literal coordinate and future moment. A separate core-only Lean module checks the same zero vectors and nonzero cleared future moments using integer normalized binary-tree recurrence. All eight statements check without axioms on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The link from the finite relation to the extension count is the mathematical argument above, not a new native theorem on arbitrary reviewed extensions.

From ai-generated, for example:

    base=research/erk-short-append-witnesses
    python3 -B "$base/find_relation.py" research/erk-eight-dispersed/tableau.json 9
    out=$(mktemp)
    python3 -B "$base/generate_core.py" --sources research --emit "$out"
    cmp "$out" lean/RKCert/ReviewedNative/ERKShortAppendCore.lean
    sha256sum -c "$base/sources.sha256"

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERKShortAppendCore
    lake env lean AuditERKShortAppendCore.lean
