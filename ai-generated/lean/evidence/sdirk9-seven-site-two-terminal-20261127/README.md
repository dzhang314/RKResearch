# Native SDIRK9 seven-site, two-terminal modular gate

The kernels of Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 checked twelve emitted degree-preserving Bézout identities and twenty-four nonzero pinned determinant residues. No Mathlib dependency or native evaluation axiom was used. The [exact replay and physical proof](../../../research/real-sdirk9-seven-site-two-terminal/README.md) distinguish reconstruction of the actual primitive-moment equations from the finite coefficient check.

From ai-generated/lean:

    sha256sum -c evidence/sdirk9-seven-site-two-terminal-20261127/sources.sha256
    lake build RKCert.ReviewedNative.SDIRK9SevenSiteTwoTerminalMod43
    lake env lean -j1 evidence/sdirk9-seven-site-two-terminal-20261127/AuditSevenSiteTwo.lean
