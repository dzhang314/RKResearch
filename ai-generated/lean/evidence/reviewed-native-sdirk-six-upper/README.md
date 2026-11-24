# Exact order six in seven strict SDIRK stages

The seven *physical* stage rows are lower triangular and every diagonal entry
is (1/2); there is no explicit first stage. The Lean certificate proves all
reviewed rooted-tree order conditions through six. For the same tableau, the
order-seven bush has factorial-scaled weight (399/400), rather than (1).

- `LaguerreGauss76Data` gives exact rational coordinates in the basis
  (1, sqrt{2}, sqrt{15}, sqrt{30}), and the checked discrepancy.
- `LaguerreGauss76` verifies the full native `HasOrder A b 6` and shows transport
  with exact order to any characteristic-zero field with the two specified roots.
- `LaguerreGauss76Real` constructs the positive roots in the actual relative
  algebraic closure of ℚ in ℝ, and supplies order-exact witnesses over both
  the real algebraic numbers and ℝ.
- `SDIRKSixSharp` is an optional consumer of the separate reviewed-native
  order-six lower-bound delta: it proves the minimum stage count is seven over
  both fields, with no weight sign, stiff accuracy, or stability condition on
  competing tableaux.

The archived exact construction uses a four-row Laguerre donor and a
three-row reflected Gauss suffix. Before scaling the whole tableau by
(1/2), the donor nodes are (1,2-sqrt2,2+sqrt2,(395-50sqrt{15})/431).
The last three rows carry the three-point Gauss weights ((5/18,5/18,4/9)).
The independent `replay.py` derives the tableau without floating-point numbers,
checks all 49 entries against the source, and reports the classical unordered
tree counts. The Lean checker uses the reviewed ordered tree constructors and
therefore pays a different count (65 terms through order six). The certificate
does not assume the construction's simplifying conditions, trust SymPy
or its source, certify stability, or claim literature priority.
