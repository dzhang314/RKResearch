# The 37 signed-ghost arithmetic gates

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check 37 explicit
unit-coordinate certificates. The [raw-weight mathematical argument](../../../research/real-sdirk9-open-signed-ghost/README.md)
and independent Python replay derive the gates from the construction
and transport them to characteristic zero. These are not a native
exclusion of unrestricted thirteen-stage tableaux.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk9-open-signed-ghost-20261127/sources.sha256
lake build RKCert.Research.SDIRK9SignedGhostMod13
lake env lean -j1 evidence/sdirk9-open-signed-ghost-20261127/AuditSignedGhost.lean
```
