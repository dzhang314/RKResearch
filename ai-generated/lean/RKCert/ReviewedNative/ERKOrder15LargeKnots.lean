module

public import RKCert.ReviewedNative.ERKOrder15LargeHeadFactor
public import RKCert.ReviewedNative.PhysicalHeadKnot

@[expose] public section

/-! # The actual grade-six window gives both physical mesh knots -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] {s a r : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G P : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

/-- The true last column vanishes by strict triangularity; the native
matrix advances the rest of a marked defect by one grade. -/
theorem marked_defect_mat [CharZero K] (ha : ∀ i t, i≤t → A i t=0)
    (j : ℕ) : markedDefectSpace A b j ≤ (markedDefectSpace A b (j+1)).comap (mat A) := by
  have endZero : mat A (coordinate (K:=K) (Fin.last s))=0 := by
    ext i
    change mat A (coordinate (K:=K) (Fin.last s)) i=0
    apply causal_mat ha
    intro t ht
    have nt : t≠Fin.last s := by
      intro e
      subst t
      change Fin.last s < i at ht
      exact (not_le_of_gt ht) (Fin.le_last i)
    simp [coordinate,nt]
  have mark {z : Fin (s+1)→K} (hz : z∈terminalMark A b) : mat A z=0 := by
    by_cases h : firstSeed A b=0
    · rw [terminalMark,ite_eq_left h] at hz
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul,endZero,smul_zero]
    · rw [terminalMark,ite_eq_right h] at hz
      rw [(Submodule.mem_bot K).mp hz,map_zero]
  intro x hx
  obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  change mat A (y+z)∈markedDefectSpace A b (j+1)
  rw [map_add,mark hz,add_zero]
  exact Submodule.mem_sup_left (mat_zeroSpace_charZero A j hy)

/-- A polynomial multiplier stays paid if all of its actual clock
powers lie in the same destination. -/
theorem weighted_eval_mem_of_powers {V : Submodule K (Fin (s+1)→K)} {m : ℕ}
    (pow : ∀ k≤m,(diag (nodes A)^k) w∈V)
    (Q : K[X]) (deg : Q.natDegree≤m) : weightedEval (nodes A) w Q∈V := by
  rw [Q.as_sum_range' (m+1) (by omega),map_sum]
  apply V.sum_mem
  intro k hk
  have e : weightedEval (nodes A) w (monomial k (Q.coeff k))=
      Q.coeff k • (diag (nodes A)^k) w := by ext i; simp [mul_assoc]
  rw [e]
  have kb := Finset.mem_range.mp hk
  exact V.smul_mem _ (pow _ (by omega))

private theorem weighted_at_six (S : Order15PaidStaircase A b a G r U w) (large : 3≤r)
    (Q : K[X]) (deg : Q.natDegree≤3) :
    weightedEval (nodes A) w Q∈markedDefectSpace A b 6 := by
  have line := S.early 1 (by decide)
  change markedDefectSpace A b 6=chain (diag (nodes A)) U w (r+1) at line
  exact weighted_eval_mem_of_powers
    (fun k hk => ((clock_chain_le_iff _).mp line.ge).2 k (by omega)) Q deg

/-- The large physical head grants every paid localized knot with a
three-degree multiplier budget, and the original Jacobi mesh vanishes
there (it need not be replaced by the zero polynomial). -/
theorem Order15PaidStaircase.large_head_knot [CharZero K] (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15) (large : 3≤r)
    (dis : ∀ i, LiveCore.live U i → w i=0)
    (repr : ∀ i, w i≠0 → w i=P.eval (nodes A i))
    (pn : P≠0) (pd : P.natDegree≤3) (Q : K[X]) (qn : Q≠0) (qd : Q.natDegree≤3) :
    ∃ k : Fin (s+1), ¬LiveCore.live U k ∧ w k=0 ∧ G.eval (nodes A k)=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R : K[X], R.natDegree+Q.natDegree≤3 →
        (formalPrimitive (R*(Q*P))).eval (nodes A k)=0 := by
  have closed (u : Fin (s+1)→K) (hu : u∈U) (v : Fin (s+1)→K) (hv : v∈U) :
      u*v∈U := S.core_times_five ha ho (S.earlyCore hv) hu
  have prev : U≤markedDefectSpace A b 6 :=
    S.earlyCore.trans (sup_le_sup (zeroSpace_mono A (by decide)) le_rfl)
  have sep : ∀ F : K[X], F.natDegree≤6 → evalNodes A F∈markedDefectSpace A b 6 → F=0 :=
    eval_eq_zero_of_coeff_separated (marked_coeff_separated ha ho S.frame.lastActive
      (by have := S.frame.size; omega) (q:=6) (j:=6) (by decide) (by decide))
  have next := S.early 2 (by decide)
  change markedDefectSpace A b 7=chain (diag (nodes A)) U w (r+2) at next
  apply physical_head_knot (j:=6) (n:=r+2) (N:=r+3) ha S.stable closed dis repr pn (by omega)
    prev (weighted_at_six S large) sep ?_ ?_ (S.escape ▸ S.first.paid) Q qn qd
  · rw [←next]
    exact marked_defect_mat ha 6
  · rw [←next]
    exact le_sup_left

end RKResearch.Certified.Graded
