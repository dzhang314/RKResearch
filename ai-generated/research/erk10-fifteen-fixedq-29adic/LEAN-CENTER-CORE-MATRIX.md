# Four Lean releases for the normalized center arithmetic

The identical core-only source was checked on Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1. All seven arithmetic identities passed each
kernel check. The 4.34.1 audit uses `propext` only; the other three
audits report the standard axiom set. No trusted compiler result
or `sorryAx` is used.

This confirms the portable polynomial arithmetic only. The actual
paid donors and tableau row adapters are separate Lean obligations.
