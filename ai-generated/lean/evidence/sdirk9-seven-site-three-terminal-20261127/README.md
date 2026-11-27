# Native SDIRK9 seven-site, three-terminal modular gate

The kernels of Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 checked the twelve emitted degree-preserving Bézout identities and twenty-four nonzero pinned determinants over the residue field, without Mathlib or a native evaluation axiom. The [exact matrix replay](../../../research/real-sdirk9-seven-site-three-terminal/README.md) reconstructs those identities from the actual primitive-moment equations and proves how their characteristic-zero forms exclude the chart.

From ai-generated/lean:

    sha256sum -c evidence/sdirk9-seven-site-three-terminal-20261127/sources.sha256
    lake build RKCert.ReviewedNative.SDIRK9SevenSiteThreeTerminalMod43
    lake env lean -j1 evidence/sdirk9-seven-site-three-terminal-20261127/AuditSevenSite.lean
