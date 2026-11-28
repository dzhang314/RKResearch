# A sixteen-stage explicit order-ten tableau in characteristic 17

The [literal tableau](tableau.json) has **exact order ten with sixteen
explicit stages** over the field with 17 elements. It specializes to
every nonzero commutative ring of characteristic 17 by the unital
map from that prime field. The order conditions are polynomial
identities with paid tree densities. The exhibited next-order defect
is a unit and therefore remains nonzero under every such map.

The construction uses a retuned eight-row dense order-five prefix
and a nine-row reverse block, identifying the latter's last row
with the prefix's actual endpoint, at clock 14 in the residue field.
The retuning uses the [Owren–Zennaro continuous family](https://doi.org/10.1090/S0025-5718-1991-1068811-2).
The [archived prefix](prefix.json) has a three-dimensional size-six
residual space. The [prefix replay](prefix-replay.log) checks all 17
dense identities through five, the actual rank across all 20 size-six
profiles, and equality of the integrated decoder to the actual endpoint
row. Run `python3 -B check_prefix.py` to reproduce those checks.
It is a different rank-three prefix chart from the rejected
[compressed four-read splice](../erk10-four-read-dense-prefix-obstruction/README.md).
The archived auxiliary reverse matrix and weights are provenance;
the independent verifier uses only the literal triangular A and
the output weights to check the method.

Run `python3 -B check_literal.py` using the standard library.
It checks all 1,205 rooted-tree equations directly, with counts
1, 1, 2, 4, 9, 20, 48, 115, 286, and 719 in orders 1–10.
For the size-eleven star, the weighted elementary value is 8
and the cleared order defect is `11 * 8 - 1 = 2 mod 17`.
The [replay transcript](exact-replay.log) includes that failure.

The [native prime-field certificate](LEAN.md) checks exact order,
strict explicitness, and the actual order-eleven failure in
Lean/Mathlib 4.36.0. The prime-power proof is mathematical.

This is an upper bound, not a 16-stage minimum. The [separate exact
lifting proof](../erk10-sixteen-17-power-lift/README.md) extends the
construction to every power of 17 and the 17-adic integers. Neither
result changes the real 14–15 interval or the single-tableau 17-stage
upper bound over the factorial localization.
