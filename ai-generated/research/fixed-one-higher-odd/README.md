# Fixed-one higher odd-order certificates

This packet extends the [frozen rational order-thirteen witness](../fixed-one-odd-continuation/README.md)
with a deterministic block solve and one reusable Lean certificate
template. All output tableaux have rational coefficients, are lower
triangular, and have common nonzero diagonal 1. The output method is
exactly the physical folded tableau of the generated virtual block;
the quotient does not count its copied donor rows as extra stages.

To generate the actual literal matrices and their Lean receipts, run
from the repository root with Python and SymPy:

```sh
out="$(mktemp -d)"
python3 ai-generated/research/fixed-one-higher-odd/gen_higher.py \
  ai-generated/research/fixed-one-odd-continuation/tableau-13.json \
  --through 15 --out "$out"
```

The output literal uses \(A=M/d\), \(\boldsymbol{b}=\boldsymbol{w}/e\);
`a_integer` and `b_integer` give the respective numerators.
The generator writes the actual folded values with their scaled
integer denominators, the next-bush defect, the virtual block and
finite matrix identities, and the stage-count-specific theorem.
No rooted tree is enumerated. The larger JSON literals are generated
rather than committed; the Lean block data and physical logic are
the primary checked artifacts.

The reusable proof has two additional ingredients. The finite sum over
a deleted head fiber is expressed as the retained coordinate plus at
most the finitely many copied coordinates; this avoids traversing a full
old tableau for every access in a long chain. Also, a protected head row
has no load on the old strict-row receipt coordinates and can therefore
use the extra degree of the mixed moment decoder. The resulting local
monomial profile on \(\boldsymbol{N}_t=F(t)\boldsymbol{\Phi}_t(A)\) is transported
through the actual causal quotient, yielding the next bank with **only**
paid chronological stages. Neither equality assumes repeated clocks
imply equal stages.

The [order-15 receipt](../../lean/evidence/fixed-one-symbolic-order15-20261127/README.md)
certifies 46 stages and four physical samples through size nine. The
generator also supports the subsequent two targets. Consult each
order-specific receipt for its **verified** Lean status; generation
alone is not a kernel check. No unconditional real-algebraic or
stability improvement is claimed.
