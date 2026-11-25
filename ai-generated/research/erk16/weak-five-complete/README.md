# Complete order-sixteen weak-five scalar proof

[Main proof](PROOF.md): the actual paid `WeakFive16.Moments` cannot hold over an ordered field. The result is also valid without nonvanishing of the polynomial at the inserted origin. The proof uses the six original local moment equations, the six global moments, and the original nonorigin mark activity. It invokes no private notes or Lean cutoff as a premise.

| Sector | Proof |
|---|---|
| Two exterior marks, or wrong exterior direction | Main proof, exact positive reciprocal interpolation and primitive-square gluing |
| One outer exterior mark | Main proof, guarded interpolation; includes the reflected endpoint-zero seam |
| One inner exterior mark | Main proof earns the signs by true erasures; [uniform density proof](../one-inner-exterior/PROOF.md) excludes them |
| Two unit changes, monic quartic | [Positive tail](crossed-interior-positive-tail.md) and [negative tail](crossed-interior-negative-tail.md), using actual crossed geometry from the main proof |
| Two unit changes, constant or affine residual | Main proof, finite small-positive-parameter sign argument over the ordered real closure |
| Three unit changes | [Exact seven-site proof](three-change/PROOF.md), including the cubic endpoint |
| Four unit changes | [Exact eight-site proof](../interior-four-changes/PROOF.md), including all eighth-weight signs and overlapping cages |

The global variation charge already excludes degrees zero and one and at least three exterior marks. No free parameter has to be fixed numerically, and no positivity of the original RK weights is presumed.

## Verify the rational data

Run these commands from this directory with standard Python 3, **without** `-O`:

```sh
python3 check_references.py
python3 ../one-inner-exterior/check_uniform_outer.py
python3 ../interior-three-changes/check_three_changes.py
python3 ../interior-four-changes/check_four_changes.py
```

The common 19-node positive mesh has all twenty moments rechecked exactly. The two crossed-tail reference calculations are also verified. The one-inner certificate verifies 15 intervals (signed upper caps −490/10⁶ and −38/10⁶); the three-change certificate checks 1,212 rectangles and all nine retained orders; the four-change certificate checks 127 cells (including four strict real-rootedness exclusions) and all 141 order possibilities in every remaining cell. All proof-critical enclosure and sign calculations are rational.

The unchanged rational tables and checkers are shared with the earlier sector proofs in this repository.

## Scope

The native scalar input is the unchanged packet returned by `width24_weak_five_moments_of_ordinary_head` in the reviewed library. This package proves the entire weak-five scalar incompatibility at the mathematical level. It neither constitutes a Lean kernel check of the combined proof nor analyzes the independent weak-four branch, and it makes no unconditional ERK16 stage-bound claim.
