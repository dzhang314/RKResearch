module

public import RKCert.ReviewedNative.ERKGradeFiveDependent
public import RKCert.ReviewedNative.ERKGradeFiveIndependent
public import RKCert.ReviewedNative.ERKOrder15ForwardEdge

@[expose] public section

/-! # Unconditional native grade-five surplus and the order-fifteen head -/
namespace RKResearch.Certified.Graded

open RKResearch Module OneOff RKCert.OneEscape

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- The genuine early surplus needs neither a weight vector nor a
stated RK order. Strict causality and native separation suffice. -/
theorem grade_five_surplus (ha : ∀ i j,i ≤ j → A i j=0) (sep : PolySeparated A 5) :
    5≤finrank K (zeroSpace A 5) := by
  by_cases dep : diag (nodes A) (g A)∈Submodule.span K {g A}
  · exact grade_five_surplus_of_dependent_quadratic ha sep dep
  · exact grade_five_surplus_of_independent_quadratic ha sep dep

/-- In particular every native order ≥10 pays the early surplus on an
arbitrary strictly lower tableau over a characteristic-zero field. -/
theorem grade_five_surplus_of_reviewed_order {p : ℕ} (ha : ∀ i j,i ≤ j → A i j=0)
    (ho : HasOrder A b p) (pay : 10≤p) :
    5≤finrank K (zeroSpace A 5) := by
  cases s with
  | zero =>
    obtain ⟨i,_⟩:=Reverse.exists_lastActive ho (by omega)
    exact Fin.elim0 i
  | succ m =>
    exact grade_five_surplus ha (PolySeparated.of_coeff
      (explicit_coeff_separated ha ho (q:=5) (by omega)))

/-- No defect-rank hypothesis remains in the ordinary forward entrance
to the order-15 marked-mesh argument. This is not the final mesh. -/
theorem order15_ordinary_forward_head (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (cap : s ≤ 22) :
    s=22 ∧ ∃ (r : ℕ) (U : Submodule K (Fin s → K)) (w : Fin s → K),
      2≤r ∧ finrank K U+r=5 ∧ U.map (diag (nodes A))≤U ∧ U≤zeroSpace A 5 ∧
      (∀ S : Submodule K (Fin s → K), S.map (diag (nodes A))≤S → S≤zeroSpace A 5 → S≤U) ∧
      (∀ n, n≤2 → zeroSpace A (5+n)=chain (diag (nodes A)) U w (r+n)) ∧
      zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A))=chain (diag (nodes A)) U w (r+3) ∧
      finrank K (zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A)) : Submodule K (Fin s→K))=8 ∧
      (diag (nodes A)^(r+2)) w∉zeroSpace A 7 :=
  order15_head_of_grade_five ha ho cap (grade_five_surplus_of_reviewed_order ha ho (by decide))

end RKResearch.Certified.Graded
