module
public import RKCert.ReviewedNative.OrderNineMultiFour
public import RKCert.ReviewedNative.OrderNineOneOffExclusion

@[expose] public section

/-! # Native ordered stage floor for every tableau with at most four defective clocks -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Polynomial Module OneOff
open scoped Matrix Classical
variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

theorem off_pos [CharZero K] (ha : ∀ i j, i≤j → A i j=0) (sep : PolySeparated A 4) :
    0 < (offKnots A).card := by
  by_contra! no
  have gz : g A=0 := by
    funext i
    by_contra h
    have pos := Finset.card_pos.mpr ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩
    omega
  exact not_invariant_with_g ha sep (by decide) (U:=⊥) bot_le (gz ▸ Submodule.zero_mem _)
    (fun _ hv=> by rw [(Submodule.mem_bot K).mp hv,map_zero]; exact Submodule.zero_mem _)
    (fun _ hv=> by rw [(Submodule.mem_bot K).mp hv,map_zero]; exact Submodule.zero_mem _)

theorem order9_low_census [CharZero K] (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b 9) (cap : s≤12) : (offKnots A).card=1 ∨ 5≤(offKnots A).card := by
  obtain ⟨size,r3,r4,_⟩ := order9_forward_chart ha ho cap
  subst s
  have sep : PolySeparated A 4 := PolySeparated.of_coeff (coeff_separated ho (by decide))
  have pos := off_pos ha sep
  obtain ⟨n2,n3⟩ := not_two_or_three ha sep r3 r4
  have n4 := order9_no_four_off_nodes ha ho
  omega

theorem order9_at_least_five_off [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 9) (cap : s≤12) :
    5≤(offKnots A).card := by
  rcases order9_low_census ha ho cap with one|m
  · exact (Nat.not_le_of_lt (by omega : s<13) (explicit_order_nine_one_off_at_least_thirteen ha ho one)).elim
  · exact m

theorem explicit_order_nine_at_most_four_off_at_least_thirteen [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 9) (few : (offKnots A).card≤4) : 13≤s := by
  by_contra! hs
  have m := order9_at_least_five_off ha ho (by omega)
  omega

end RKResearch.Certified.Graded.MultiOff
