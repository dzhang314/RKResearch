# Lean/Mathlib 4.36.0 replay: DIRK10, strict SDIRK6, and ERK8

From `ai-generated/lean` in the configured project:

    lake build RKCert.Research.SDIRKSixSquarefreeRings RKCert.ReviewedNative.ERK8ElevenFourTapRational RKCert.ReviewedNative.DIRKOrderTenCrossedZeros
    lake env lean AuditReviewedNativeDIRKOrderTenCrossedZeros.lean

The attached logs record a direct Lean kernel replay of the new modules
against the compiled project dependencies. The audited results use only
`propext`, `Classical.choice`, and `Quot.sound`. The ERK result is a scalar
elimination for the stated architecture, not a lower bound ruling out all
eleven-stage rational methods. The DIRK result is a necessary condition,
not an exclusion of all eleven-stage tableaux.
