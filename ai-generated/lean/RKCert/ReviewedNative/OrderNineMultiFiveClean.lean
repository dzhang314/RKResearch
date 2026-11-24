module
public import RKCert.ReviewedNative.OrderNineMultiCleanRadau

@[expose] public section

/-! # Terminal exclusion on the six- and seven-off five-clean chart -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- If five clean nodes and six or seven off nodes fill a candidate, the
paid adjoint forces the last live coordinate to have clock one and to be
a clean state. The five-clean quadrature forbids that endpoint. -/
theorem order9_no_five_clean_six_or_seven {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b) (m : (cleanKnots A).card=5)
    (n : (offKnots A).card=6 ∨ (offKnots A).card=7) : False := by
  obtain ⟨P,dP,_,_,hF,fit⟩ := order9_two_curve_head ha ho (by decide) (by rcases n with h|h <;> omega)
  have cancel := offMass_zero_of_head ho fit (by rcases n with h|h <;> omega)
  have nondiv := order9_five_on_head_not_dvd (s:=11) ha ho m cancel hF P dP fit
  have last := Reverse.lastActive_of_odd_floor ha ho (q:=4) (by decide) (by decide) (by decide)
  have rk := onOffSpace_rank A
  apply one_not_on_of_five (s:=11) ha ho m cancel
  rcases n with six|seven
  · have inc := five_on_state_le (q:=4) (by decide) m six P dP fit nondiv
    have hi := order9_grade_six_upper ha ho
    have eq : onOffSpace A=treeSpace A 6 := Submodule.eq_of_le_of_finrank_le inc
      (by rw [rk,m,six]; exact hi)
    have dim : finrank K (treeSpace A 6)=11 := by rw [←eq,rk,m,six]
    obtain ⟨_,one,_,unit⟩ := Reverse.reverse_capacity_terminal ha ho (j:=6) (n:=1)
      (by decide) (by omega) last
    have v : Pi.single (Fin.last 11) 1∈onOffSpace A := by
      rw [eq,←coordinate_as_single]; exact unit _ le_rfl
    exact mem_cleanKnots.mpr ⟨_,on_of_state_single v last.live cancel,one⟩
  · have inc := five_on_state_le (q:=5) (by decide) m seven P dP fit nondiv
    have low := Submodule.finrank_mono inc
    have cap : 12≤finrank K (treeSpace A 7)+0 := by rw [rk,m,seven] at low; omega
    obtain ⟨_,one,_,_⟩ := Reverse.reverse_capacity_terminal ha ho (j:=7) (n:=0) (by decide) cap last
    have top : onOffSpace A=⊤ := Submodule.eq_top_of_finrank_eq (by rw [rk,m,seven,Module.finrank_fin_fun])
    have v : Pi.single (Fin.last 11) 1∈onOffSpace A := by rw [top]; trivial
    exact mem_cleanKnots.mpr ⟨_,on_of_state_single v last.live cancel,one⟩

theorem order9_no_seven_off {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b) : (offKnots A).card≠7 := by
  intro seven
  have mlo := (order9_multi_quadrature ha ho (by decide) (by omega) (by omega)).2
  have cnt := clean_off_count A
  exact order9_no_five_clean_six_or_seven ha ho (by omega) (.inr seven)
end RKResearch.Certified.Graded.MultiOff
