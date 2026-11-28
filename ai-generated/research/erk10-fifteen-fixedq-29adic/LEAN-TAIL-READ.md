# Portable ring-level transport of the exact e/f scalar gates

The three modules `ERK10FixedQ29AdicZTailCore`,
`ERK10FixedQ29AdicZTailSound`, and `ERK10FixedQ29AdicZTailRead`
carry the integer tail checks to arbitrary commutative
coefficient rings with specified paid denominators.
The core ring typeclass is `Lean.Grind.CommRing`;
Mathlib's existing `CommRing.toGrindCommRing` supplies this
interface from the actual coefficient ring.

1. `eval_take_zeroTop`, `next_top` and `eval_next` prove
   that each pseudo-reduction drops **only** a zero leading
   coordinate and multiplies the Horner value by the decic
   leading coefficient when evaluated at the actual root.
2. `reduce_represents`, `represents_add`, `represents_mul`
   and `represents_neg` transport the denominator-cleared
   interpretation by induction and literal Horner algebra.
   `reduce_den` supplies the exact power of the leading
   coefficient paid by the input length.
3. `Reads` then tracks both the interpretation and an
   explicit denominator inverse. `div_seven_read`,
   `scale_read_sound` and `out_e_f_read` prove the seven
   exact quotient values, scale equation and both
   normalized terminal-output equations in the coefficient
   ring itself. The proof uses the original checked
   constants and exact kernel zero, not a modular cutoff.

All 19 reports, including the earlier 11 integer checks,
five operator lemmas and three new endpoint theorems,
passed stock Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1
with only standard axioms. To reproduce the portable
single-document check from a repository checkout:

    stem=ai-generated/lean/RKCert/ReviewedNative/ERK10FixedQ29AdicZTail
    tmp=$(mktemp --suffix=.lean)
    cat "$stem"Core.lean > "$tmp"
    tail -n +4 "$stem"Sound.lean >> "$tmp"
    tail -n +4 "$stem"Read.lean >> "$tmp"
    "$LEAN" --threads=1 --memory=850 "$tmp"
    rm "$tmp"

The normalized equations are not yet a native physical
word-row receipt. The separate draft chain is
`ZTailActual` (local root/slot specialization and
seven paid-site interpolation), `ZTailPhysicalAlign`
(normalized output equals actual cubic observer),
`ZTailPhysicalRows` (cardinal scaling and actual
\(e,f\) equality) and `WordAll` (all eleven physical
rows). This draft chain has **not been kernel-checked**.
It needs the existing physical `WordD` and the
above portable modules, but no new packed
arithmetic gate. The exact mathematics beyond it,
with the final tree and failure obligations, is in
`WORD-FILTER-TO-ORDER.md`.
