# Early marked ERK(13): excluding width 19

This package proves the early terminal branch of the width-19 exclusion over every characteristic-zero field. The inputs are the actual strict explicit tableau, its reviewed rooted-tree `HasOrder 13` conditions, zero first reflected seed, and membership of the literal final coordinate in the genuine grade-seven tree space. This is a paper proof with reproducible exact polynomial certificates and a standalone Lean-checked scalar lemma. It is not a claim that the whole early branch has compiled in Lean.

## Proof order

1. [Paid marked staircase](PAID-STAIRCASE.md): reviewed original-coordinate rank and clock steps; actual head, first-escape chart, paid shift locality, radius cut, and first terminal timing.
2. [Lobatto branch and two-head flag](A5-LOBATTO.md): exact endpoint leakage, cubic and factor gates in the degree-six mesh, radius reduction, and the remaining radius-two class chart. It also earns the two-head flag used by the pencil branch.
3. [Degree-seven pencil](A6-PENCIL.md): two uniform, characteristic-zero scalar gates, clean lower ranks, and absorption of all pure factor exits. Only the radius-two complete-intersection chart remains.
4. [Final three classes](FINAL-THREE.md): one causal last-three support argument closes both high square charts. It uses five genuine folded reverse rows, two adjoint polynomial bounds, and class weight/head information; no positivity, ordering of the field, or nonzero weight assumption on every row is required.

[NativeFinalThreeScalar.lean](../../../lean/RKCert/ReviewedNative/NativeFinalThreeScalar.lean) was checked by Lean and independently replayed. It proves only the fraction-free compatibility of four scalar equalities. It does not silently assert the causal geometry or the pencil certificates in Lean.

## Reproducing the exact checks

The Lobatto check uses Python's integers and fractions. The pencil and final-three checks use exact SymPy polynomial arithmetic.

```sh
python3 certificates/early_a5_certificate.py
python3 certificates/early_a6_pencil_certificate.py
python3 certificates/early_class_tail_certificate.py
```

The wider late-terminal and nonzero-seed classifications are outside this package. No unrestricted width-20 theorem is asserted here.
