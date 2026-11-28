# Native endpoint flag and portable integer Hilbert receipt

From the repository's certificate Lake project (with dependencies
already built):

    cd ai-generated/lean
    lake build RKCert.ReviewedNative.CausalStage
    lake env lean --threads=1 RKCert/ReviewedNative/ERK10EndpointPlateau.lean
    lean --threads=1 RKCert/ReviewedNative/ERK10EndpointHilbertFive.lean

The plateau module is checked against the project's Lean/Mathlib
4.36.0. Its printed endpoint theorems use only propext,
Classical.choice and Quot.sound. It has no positive/ordered field
hypothesis. The generic rank ledger, abstract mark leakage cost,
causality-aware physical first primitive and two-paid-moment target
nonvanishing are native. The math note proves that the actual
short word budget supplies the module's rank flag; this is not
an end-to-end Lean statement from a full rooted tableau.

The integer Hilbert receipt has no Mathlib import and the same
file passes stock Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.
It proves the literal entry and both inverse product identities
at scale 2520 using kernel reduction. There is no sorry,
native_decide or external solver in either module's endpoints.
The named project module was not tested against non-4.36 Mathlib
builds; the four-way verification applies to the core receipt.
