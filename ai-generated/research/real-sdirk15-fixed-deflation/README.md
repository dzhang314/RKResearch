# No single chronological linear deflation on the fixed real SDIRK15 tableau

The actual archived 34-stage order-15 tableau has **full stage rank 34**
on rooted trees through size 14. A directed exact replay certifies
only 34 pivot columns are needed; the short binary-tree labels in
the receipt are enough to reproduce them. This is not a scalar
output-rank assumption or a generic lower bound.

Every row but the first either has a nonzero actual output weight
or has a nonzero strict coefficient into a stage with nonzero
output weight. Both are verified at the same independent algebraic
tableau. A direct chronological linear deflation would need to
replace the actual row signal by an earlier row combination through
at least size 14 (size 15 if its own output weight is nonzero);
full rank already excludes every such relation at size 14.
The first row has no earlier stage and cannot be synthesized even
on the leaf. It does have a nonzero strict path to output.

This rules out the simple fixed-tableau substitution, not a
redesign of the middle coefficients or a reduction that preserves
only scalar outputs without recovering the replaced row signal.
It does not improve the real upper bound or add a Lean theorem.

## Reproduce

From this directory:

```sh
res="$PWD"
work="$(mktemp -d)"
python3 export_archived34.py "$work/export.js"
(cd "$work" && node export.js)
(cd "$work" && python3 "$res/rank_binary.py" "$res/../real-sdirk13-forward-ports")
```

The exporter runs the existing root inclusion, ordinary-prefix,
reverse word, causal representative, and double-merge checks.
It replaces only the last optional rooted diagnostics with an
export of the actual assembled coefficient intervals. All rank and
physical reachability decisions in the second script are directed
integer interval checks; it does not compare decimal singular values.
