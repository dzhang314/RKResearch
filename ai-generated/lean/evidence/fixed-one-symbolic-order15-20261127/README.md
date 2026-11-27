# Standard-axioms order-15 receipt: 46 fixed-one strict SDIRK stages

On Lean 4.36.0, `RKResearch.Certified.FixedOneOrder15.witness`
proves the reviewed `HasOrder 15` and failure of `HasOrder 16`
for a rational lower triangular tableau of size 46 and common
nonzero diagonal 1. No native computation axiom is used. The same
build pays local purity through size nine for four actual physical
receivers at zero-based indices 35, 36, 37, 38. The virtual block
adds fourteen rows to the unchanged 35-stage order-thirteen seed,
then deletes precisely three literal donor copies. This is a
rational upper bound (previously 48), not a new lower bound or an
improvement to the unrestricted real-algebraic upper.

`Seed13Fast.lean` imports the frozen order-thirteen theorem, proves
all three relevant physical rows pure through size eight, and
switches its coefficient evaluator to the equivalent fast-fold
formula. It does not change the physical tableau, source, or
check status of the old witness. `Stage15Data.lean` contains the
finite coefficients. `Stage15.lean` checks the finite assignments
and proves order by the symbolic tail lemma, not a tree replay.
`Audit15.lean` independently imports the existential theorem and
the next-bank statement with literal sizes and orders, then checks
their transitive axioms and the actual copy identity.

## Ordered replay

From the repository root:

```sh
repo="$PWD"
p13="$repo/ai-generated/lean/evidence/fixed-one-symbolic-order13-20261127"
p15="$repo/ai-generated/lean/evidence/fixed-one-symbolic-order15-20261127"
work="$(mktemp -d)"
cp "$p13"/{Seed11Donors,Symbolic13Data,Symbolic13}.lean "$work/"
cp "$p15"/{Seed13Fast,Stage15,Stage15Data,Audit15}.lean "$work/"
(cd "$work" && sha256sum -c "$p15/sources.sha256")
python3 ai-generated/research/rooted-tree-gram/gen_lean.py \
  ai-generated/research/fixed-one-newton/tableau-11.json --graded \
  > "$work/Certificate11.lean"
cd ai-generated/lean
lake build RKCert.ReviewedNative.GramLocalPurity \
  RKCert.ReviewedNative.FastCausalFold RKCert.ReviewedNative.ProtectedTail
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$1"
  for mod in Certificate11 Seed11Donors Symbolic13Data Symbolic13 Seed13Fast Stage15Data Stage15; do
    lean -j1 -o "$mod.olean" "$mod.lean" || exit
  done
  lean -j1 Audit15.lean
' _ "$work"
```

Regenerate the two Lean sources and the integer-scaled physical
tableau with `gen_higher.py --through 15` as described in the
[continuation directory](../../../research/fixed-one-higher-odd/README.md);
verify the resulting three artifacts using `generated.sha256`.
The source hash of the unchanged p13 seed literal is recorded
in `seed13.sha256`. The original compile of `Stage15.lean`
took 27.07 seconds with the preceding dependencies compiled.
This receipt establishes 4.36.0, not a claim that the full
witness has been replayed on the other requested toolchains.
