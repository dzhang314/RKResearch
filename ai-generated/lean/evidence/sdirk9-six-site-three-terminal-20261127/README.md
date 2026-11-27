# Native SDIRK9 six-site, three-terminal modular gate

The kernels of Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 checked all four literal degree and Bézout identities for the emitted coefficient pairs over the residue field, without Mathlib or native evaluation axioms. The [exact replay](../../../research/real-sdirk9-six-site-three-terminal/README.md) reconstructs them from the moment matrices and verifies the number-field reduction witnesses. The actual rooted and characteristic-zero resultant arguments are separate.

From ai-generated/lean:

    sha256sum -c evidence/sdirk9-six-site-three-terminal-20261127/sources.sha256
    lake build RKCert.ReviewedNative.SDIRK9ThreeTerminalMod37
    lake env lean -j1 evidence/sdirk9-six-site-three-terminal-20261127/AuditThreeTerminal.lean
