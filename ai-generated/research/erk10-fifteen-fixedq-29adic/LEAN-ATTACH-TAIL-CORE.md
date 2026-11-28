# Portable attach induction and actual tail arithmetic

Two stock-Init Lean modules were checked on 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1, with only standard axioms. To replay
from the repository root, set `LEAN` to the stock version's
Lean binary and run:

    "$LEAN" --threads=1 --memory=700 ai-generated/lean/RKCert/ReviewedNative/ERK10FixedQ29AdicAttachCore.lean
    "$LEAN" --threads=1 --memory=700 ai-generated/lean/RKCert/ReviewedNative/ERK10FixedQ29AdicZTailCore.lean

## Generic recursion

`ERK10AttachCore.Kit.grade` proves the complete nonlinear
attach-filtration induction. It uses any tree presentation
with a positive size and a binary attach whose sizes add.
For `RKCert.Tree`, take `size := Tree.order` and
`attach t l r := t = Tree.attach l r`. The positive-size
lemma already exists; for a tree of size at least six,
cases on it give the required attach and rule out the leaf.
No alternative rooted-tree recursion or enumeration is
required.

The module has no actual Runge–Kutta hypothesis built in.
The ring/physical adapter must supply the true block
expansion and filter properties: `err` is the actual raw
stage defect, `edge` the actual unary-edge defect, `ann`
the annihilator of the paid filter, and `line` the
span of the actual host dirt. The two degree-shift inputs
come from the nominal model degrees. The three nonlinear
product inputs follow from the exact scalar contact and
its mark. The theorem covers all three actual nonlinear
attach cases; it is not itself a lifted order theorem.

## Actual scalar data for the tail

`ERK10FixedQ29AdicZTailCore` uses the same literal decic,
symmetric head, cardinal numerator, tail nodes, quotient
and scale data as the physical construction. The stock
kernel checked that every starting denominator is prime to
29, all seven exact degree-six quotient samples, the exact
scale constraint at 26, and the exact two terminal
constraints at e and f. Arithmetic is fraction-free:
each pseudoremainder step multiplies the current numerator
by the decic leading coefficient and subtracts its leading
term times the shifted decic; it multiplies the denominator
by that same coefficient. No compiler-trusted evaluation
or result modulo a finite cutoff substitutes for these
integer zero checks.

A ring-generic operator-soundness transport, literal slot
alignment and the actual physical row consumers remain
separate from this transcript. The mathematical adapter is
in `WORD-OMITTED-ROWS.md`.
