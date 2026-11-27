# Kernel certificate receipt: fixed diagonal one

The reusable source is `RKCert/ReviewedNative/RootedTreeGram.lean`.
The independently reproducible finite sources are **Certificate9.lean**
and **Certificate11.lean**. Their source digests are recorded here;
they are generated on demand rather than storing large duplicate
constant matrices in the repository.

The exact statements in the generated modules are
`RKResearch.Certified.StrictSDIRKGram18Order9.witness` and
`RKResearch.Certified.StrictSDIRKGram26Order11.witness`.
Each certifies lower triangularity, common nonzero diagonal 1,
the reviewed `HasOrder` up to its target, and failure at the very
next order by a literal bush condition.

## Replay

From the repository root, with the selected Lean/Mathlib version
installed:

```sh
certdir="$(mktemp -d)"
for n in 9 11; do
  python3 ai-generated/research/rooted-tree-gram/gen_lean.py \
    "ai-generated/research/fixed-one-newton/tableau-$n.json" --graded \
    > "$certdir/Certificate$n.lean"
done
(cd "$certdir" && sha256sum -c "$OLDPWD/ai-generated/lean/evidence/rooted-tree-gram-fixed-one-20261127/generated-source.sha256")
cd ai-generated/lean
lake build RKCert.ReviewedNative.RootedTreeGram
for n in 9 11; do
  lake env lean -j1 --root="$certdir" -o "$certdir/Certificate$n.olean" \
    "$certdir/Certificate$n.lean"
done
```

The source hash uses `--graded` to print each finished Gram recurrence;
the optional diagnostic lines do not change the theorem. No
`native_decide` or compiler oracle is involved in the checked
proofs. See the individual replay receipts for actually verified
toolchain versions.
