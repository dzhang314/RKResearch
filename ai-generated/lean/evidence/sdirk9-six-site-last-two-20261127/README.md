# Native smaller gates for the final six-site SDIRK9 exclusions

The kernels of Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 checked the thirteen literal full-degree Bézout identities and thirty-eight nonzero pinned or cofactor residues emitted by the [independent exact replay](../../../research/real-sdirk9-six-site-last-two/README.md). No Mathlib dependency or native evaluation axiom was used. This covers the minimum-mesh and elementary six-site modular gates, **not** the 59 AP Gröbner/compactification checks or the actual-classical-order transfer, which are recorded separately.

From ai-generated/lean:

    sha256sum -c evidence/sdirk9-six-site-last-two-20261127/sources.sha256
    lake build RKCert.ReviewedNative.SDIRK9SixSiteSmallGates
    lake env lean -j1 evidence/sdirk9-six-site-last-two-20261127/AuditSixSites.lean
