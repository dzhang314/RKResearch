module

public import RKCert.Dirk15NonC2Early
public import RKCert.RadauRightMoment
public import RKCert.CompanionFactorLine

@[expose] public section

/-! # Fixed Radau and compound-eigenline support for order-fifteen DIRK

This does not prove a new stage bound. It validates the actual non-C(2)
fourth/fifth ranks, both fixed Radau arithmetic gates, and the generic
compound exterior-line part of the later free-pencil argument.
-/
