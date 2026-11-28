# Independent replay of the ERK11 central-carrier arithmetic

The [central-carrier proof](../../../research/ERK11-SOLE-LATE-CARRIER-CENTER-EXCLUSION.md)
uses a kernel-checked dyadic Bernstein certificate. A separate exact
rational replay reconstructs its two equations directly from monomial
moments, forms the Bezout determinant and its two cofactors, then checks
the Sturm count and the discriminant sign query:

    python3 -B check_center.py

The replay uses SymPy and no floating point. Its output is
[center-sturm-audit.txt](center-sturm-audit.txt). The Lean logs check
the separate Bernstein and front scalar certificates on the indicated
versions. The tableau reductions remain mathematical.
