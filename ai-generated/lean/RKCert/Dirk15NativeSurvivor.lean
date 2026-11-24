module

public import RKCert.Dirk15NonC2Finish
public import RKCert.Dirk15EarlySurplus
public import RKCert.Dirk15MinimalHiddenHead
public import RKCert.Dirk15MinimalMovingQuartic
public import RKCert.Dirk15DeletedPencilJacobi

@[expose] public section

/-! # What any hypothetical order-fifteen twenty-stage method would be

The non-C(2) and early full-marked surplus cases have been independently
excluded. This module does not exclude the surviving minimal chart and
does not state an unrestricted 21-stage bound.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_twenty_minimal_chart (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) :
    q₂ (mat A) (nodes A) 1=0 ∧ finrank K (marked A 15 4)=2 ∧
      Order15MinimalMarkedChart A b := by
  rcases order15_twenty_native_cases ha ho with ⟨h,_,_⟩|⟨a,_,m,_⟩|⟨a,d,h,_⟩
  · exact (h (order15_twenty_implies_C2 ha ho)).elim
  · have hc : 3≤finrank K (marked A 15 4) := by
      rw [m 4 (by decide) (by decide)]
    exact (order15_no_early_marked_surplus ha ho a hc).elim
  · exact ⟨a,d,h⟩

/-- Exact native geometry of the remaining branch. Either the entire
grade-four space is hidden on two original coordinates, or a true
visible quartic has an affine/constant head and an independent paid
reverse quartic on actual cubic support. -/
theorem order15_twenty_native_surviving_geometry (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) :
    (∃ h : Order15HiddenHead A b, Nonempty h.head.DeletedPencil) ∨
    ∃ (h : Order15MinimalHead A b) (v : Vec K 20), v∈zeroSpace A 4 ∧
      (∃ u∈h.U,∃ S : K[X],S≠0 ∧ S.natDegree≤2-finrank K h.U ∧
        v=u+weightedEval (nodes A) h.w S) ∧
      (∃ Q : K[X],Q≠0 ∧ Q.natDegree≤4 ∧
        (∀ i,reverseCubic A b i≠0 → v i=Q.eval (mirror A i)) ∧
        ∀ i,b i≠0 → reverseCubic A b i=0 → v i=0) ∧
      Nonempty h.DeletedPencil := by
  have ⟨_,f4,H⟩ := order15_twenty_minimal_chart ha ho
  by_cases hide : zeroSpace A 4≤simultaneousGhosts A b
  · obtain ⟨h⟩ := order15_two_hidden_head ha ho H hide
    exact Or.inl ⟨h,h.head.deleted_pencil ha ho H⟩
  · change ¬∀ v : Vec K 20,v∈zeroSpace A 4→v∈simultaneousGhosts A b at hide
    push Not at hide
    obtain ⟨v,hv,bad⟩ := hide
    obtain ⟨h⟩ := order15_minimal_head ha ho H
    obtain ⟨out,q⟩ := order15_minimal_visible_quartic ha ho H f4 h hv bad
    exact Or.inr ⟨h,v,hv,h.visible_head_degree hv out,q,h.deleted_pencil ha ho H⟩

end RKCert.Paired
