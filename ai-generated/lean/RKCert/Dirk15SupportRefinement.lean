module

public import RKCert.Dirk15Support
public import RKCert.Dirk15NonC2ReverseOrbit
public import RKCert.Dirk15OrdinaryCore
public import RKCert.Dirk15HideCubic
public import RKCert.DirkResultantTransfer
public import RKCert.FixedPolynomialSpecialize

@[expose] public section

/-! # Native cubic and chronological reductions for both p15 minimal bands
No finite Radau or free-pencil norm nonvanishing is asserted here. -/
namespace RKCert.Paired
open Polynomial RKCert.OneEscape

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_minimal_true_ghost_sandwich (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (h : Order15MinimalMarkedChart A b) :
    zeroSpace A 3≤simultaneousGhosts A b ∧ simultaneousGhosts A b≤zeroSpace A 7 :=
  ⟨order15_cubic_le_simultaneous_ghosts ha ho h (order15_minimal_reverse_nonlocal ha ho h),
    order15_simultaneous_ghosts_le ha ho h (order15_minimal_reverse_nonlocal ha ho h)⟩

theorem order15_nonC2_cubic_channels (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) {v : Vec K 20} (hv : v∈zeroSpace A 3) :
    ∀ i, b i≠0 ∨ reverseCubic A b i≠0 → v i=0 := by
  have h := order15_nonC2_rank_chart ha ho hq
  apply order15_cubic_channels_of_orbit ha ho h.terminal
    (order15_cubic_budget_orbit ha ho (h.cubic_budget ha ho)) hv
  exact h.terminal_pure_zero _ (zeroSpace_mono A (by decide) hv)

end RKCert.Paired
