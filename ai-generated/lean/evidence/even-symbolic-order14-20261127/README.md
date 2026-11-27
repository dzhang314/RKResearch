# Exact rational order 14 in 38 strict SDIRK stages

The theorem `RKResearch.Certified.EvenTerminal14.witness` proves exact order
14, failure at order 15, and a lower triangular stage matrix with constant
nonzero diagonal 1/4. The native Lean proof reconstructs a 44-stage virtual
tableau, verifies all six complete strict copied rows, and folds them into
their earlier physical representatives. It does not enumerate order-14 trees.

The intermediate order-12 preparation has 31 physical stages. Its typed
theorems give all six head rows locally exact through tree size seven and
three fresh rows exact through size eight, at actual physical indices.
The first fresh row is proved exact through seven before being used as
an additional observation for the later protected rows.

## Replay

Use the [order-12 replay](../even-moment-tail-20261127/README.md) first,
retaining its temporary directory as `work`. From the repository root:

```sh
repo="$PWD"
res="$repo/ai-generated/research/even-terminal-head-sharing"
ev="$repo/ai-generated/lean/evidence/even-symbolic-order14-20261127"
cp "$ev"/*.lean "$work/"
(cd "$work" && sha256sum -c "$ev/sources.sha256")
cd ai-generated/lean
lake build RKCert.ReviewedNative.CausalCopyLocal RKCert.ReviewedNative.FastCausalFold
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$1"
  for mod in Seed10EvenHigh EvenPrep12Data ProofEvenPrep12 Even14Data ProofEven14; do
    lean -j1 -o "$mod.olean" "$mod.lean" || exit
  done
  lean -j1 Audit14.lean
' _ "$work"
```

Regenerate the literal physical JSON and both finite Lean matrix files from
the archived order-10 tableau. Both generators independently also compare
their folded result to the corresponding JSON entry by entry:

```sh
python3 "$res/build_terminal_family.py" "$res/tableau-10.json" --out "$work/data" --through 14
(cd "$work/data" && sha256sum -c "$ev/fixtures.sha256")
python3 "$res/prep12_receipts.py" "$res/tableau-10.json" "$work/EvenPrep12Data.lean" "$work/data/prep-12/tableau-12.json"
python3 "$res/terminal_receipts.py" 14 "$work/data" "$work"
cp "$res/make_even14.py" "$work/"
python3 "$work/make_even14.py"
(cd "$work" && sha256sum -c "$ev/sources.sha256")
```

Lean 4.36.0 with matching Mathlib checked the proof source and the typed
import, including the literal witness, its copied rows, the intermediate
order, and both sizes of head observation. Standard axioms only:
`propext`, `Classical.choice`, and `Quot.sound`.
