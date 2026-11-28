# Portable scalar evidence

The core-only module
[ERK10FourfoldInteriorScalars.lean](../../lean/RKCert/ReviewedNative/ERK10FourfoldInteriorScalars.lean)
checks the intervening repeated-row feedback coefficient and the next
singleton corrected-cubic square with no use of Mathlib or compiler
evaluation. It passes Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1 with
standard axioms only. The rank, nilpotent span, and physical-chart
adapter are mathematical rather than a native tableau-level theorem.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10FourfoldInteriorScalars.lean
    sha256sum -c ai-generated/research/erk10-five-opening-fourfold-interior/lean-checked.sha256
