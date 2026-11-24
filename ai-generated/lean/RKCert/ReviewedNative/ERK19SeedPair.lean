module

public import RKCert.ReviewedNative.ERK19SeedFibers

@[expose] public section

/-! # An extra true annihilator at an off-seed live weight

Two adjacent Legendre columns furnish a row of Ann(E8) which is nonzero
at every specified live weight, regardless of the sign or clock value. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Matrix Classical
noncomputable section
variable {K : Type*} [Field K]

private def leg9Data (K : Type*) [Ring K] : Fin 11→K :=
  ![-1,90,-1980,18480,-90090,252252,-420420,411840,-218790,48620,0]
private def leg10Data (K : Type*) [Ring K] : Fin 11→K :=
  ![1,-110,2970,-34320,210210,-756756,1681680,-2333760,1969110,-923780,184756]

private def leg9At (x : K) : K :=
  -1+90*x-1980*x^2+18480*x^3-90090*x^4+252252*x^5-420420*x^6+
    411840*x^7-218790*x^8+48620*x^9
private def leg10At (x : K) : K :=
  1-110*x+2970*x^2-34320*x^3+210210*x^4-756756*x^5+1681680*x^6-
    2333760*x^7+1969110*x^8-923780*x^9+184756*x^10

set_option maxHeartbeats 900000 in
private theorem leg9_moments [CharZero K] (i : Fin 9) :
    (∑ t : Fin 11, leg9Data K t / ((i.val+t.val+1:ℕ):K))=0 := by
  fin_cases i <;> norm_num [Fin.sum_univ_succ,leg9Data]

set_option maxHeartbeats 900000 in
private theorem leg10_moments [CharZero K] (i : Fin 9) :
    (∑ t : Fin 11, leg10Data K t / ((i.val+t.val+1:ℕ):K))=0 := by
  fin_cases i <;> norm_num [Fin.sum_univ_succ,leg10Data]

private theorem adjacent_leg_no_common [CharZero K] {x : K} (h9 : leg9At x=0)
    (h10 : leg10At x=0) : False := by
  let U := -7381+534710*x-10694970*x^2+94757520*x^3-447957510*x^4+
    1231242012*x^5-2029787760*x^6+1976694720*x^7-1047566520*x^8+232792560*x^9
  let V := -7129+414810*x-6631020*x^2+46366320*x^3-169279110*x^4+
    346846500*x^5-401501100*x^6+245044800*x^7-61261200*x^8
  have e : U*leg9At x+V*leg10At x=252 := by dsimp [U,V,leg9At,leg10At]; ring
  rw [h9,h10,mul_zero,mul_zero,add_zero] at e
  exact (by norm_num : (0:K)≠252) e

variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

private theorem leg9_eval (i : Fin 29) :
    coeffEval A 10 (leg9Data K) i = leg9At (nodes A i) := by
  rw [coeffEval_apply]
  simp only [Finset.sum_apply,normTree_clockTree,Pi.smul_apply,smul_eq_mul]
  norm_num [Fin.sum_univ_succ,leg9Data,leg9At]
  ring

private theorem leg10_eval (i : Fin 29) :
    coeffEval A 10 (leg10Data K) i = leg10At (nodes A i) := by
  rw [coeffEval_apply]
  simp only [Finset.sum_apply,normTree_clockTree,Pi.smul_apply,smul_eq_mul]
  norm_num [Fin.sum_univ_succ,leg10Data,leg10At]
  ring

private theorem weighted_coeff_row (v : Fin 11→K) (w : Fin 29→K) :
    row (b*coeffEval A 10 v) w = ∑ j : Fin 11, v j * probe A b j.val w := by
  simp only [row_apply,dotProduct,Pi.mul_apply,coeffEval_apply,Finset.sum_apply,
    normTree_clockTree,Pi.smul_apply,smul_eq_mul]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact order provides the real row test; no output weight is divided
out and no ordinary scalar evaluation is required to be injective here. -/
private theorem paid_scalar_ann_eight (ho : HasOrder 19 A b) (v : Fin 11→K)
    (tested : ∀i : Fin 9, (∑j : Fin 11,v j/((i.val+j.val+1:ℕ):K))=0) :
    b*coeffEval A 10 v ∈ annih (treeSpace A 8) := by
  refine mem_annih.mpr fun w hw => ?_
  rw [treeSpace_coeff_sup ho (by decide)] at hw
  obtain ⟨_,⟨a,rfl⟩,f,hf,rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  have pure : row (b*coeffEval A 10 v) f=0 := by
    rw [weighted_coeff_row]
    apply Finset.sum_eq_zero
    intro j _
    have z : probe A b j.val f = 0 := probe_zeroSpace ho (by have :=j.isLt; omega) hf
    rw [z,mul_zero]
  rw [pure,add_zero,coeffEval_apply A 8 a,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  have eq : row (b*coeffEval A 10 v) (normTree A (clockTree i.val)) =
      probe A b i.val (coeffEval A 10 v) := by
    simp only [row_apply,dotProduct,Pi.mul_apply,normTree_clockTree]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [eq,probe_coeffEval ho (by have :=i.isLt; omega),tested i,smul_zero]

/-- Every live weight is detected by an actual grade-eight annihilator.
The exact coprime pair does not require algebraic closure. -/
theorem ann_eight_detects_live_output [CharZero K] (ho : HasOrder 19 A b) (i : Fin 29)
    (live : b i≠0) : ∃ w ∈ annih (treeSpace A 8), w i≠0 := by
  by_cases g : leg9At (nodes A i)=0
  · exact ⟨b*coeffEval A 10 (leg10Data K),paid_scalar_ann_eight ho _ leg10_moments,by
      rw [Pi.mul_apply,leg10_eval]
      exact mul_ne_zero live (fun z => adjacent_leg_no_common g z)⟩
  · exact ⟨b*coeffEval A 10 (leg9Data K),paid_scalar_ann_eight ho _ leg9_moments,by
      rw [Pi.mul_apply,leg9_eval]
      exact mul_ne_zero live g⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- In the balanced wide branch the grade-nine defect is already
constant on every nonzero-seed fibre when there are eleven sites, or
when there are ten sites with even a single live off-seed row. -/
theorem balanced_grade_nine_first_trace (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 19 A b) (band : FullFirstBand A b)
    (balance : ∀ a, clockMass (nodes A) (firstSeed A b) a=0)
    (split : (weightedSites (nodes A) (firstSeed A b)).card=11 ∨
      ((weightedSites (nodes A) (firstSeed A b)).card=10 ∧
       ∃i, firstSeed A b i=0 ∧ b i≠0)) {f : Fin 29→K} (hf : f∈zeroSpace A 9) :
    firstSeed A b*f ∈ OriginalFirstCarrier A b := by
  have m := first_seed_mixed_annih ho (j:=9) (k:=8) (by decide) (zeroSpace_le_treeSpace A 9 hf)
  have sub := balanced_first_carrier_le_annih_eight ho band balance
  have dim := first_carrier_rank (A:=A) (b:=b)
  have cap := width29_annih_eight_rank ha ho
  rcases split with h | ⟨h,i,d0,active⟩
  · have eq := Submodule.eq_of_le_of_finrank_le sub (by omega)
    exact eq.symm ▸ m
  · obtain ⟨w,hw,wi⟩ := ann_eight_detects_live_output ho i active
    have outside : coordinate (K:=K) i∉treeSpace A 8 := by
      intro h
      exact wi (by simpa only [row_coordinate] using mem_annih.mp hw _ h)
    have r := finrank_zeroAt_annih (treeSpace A 8) i outside
    have inc : OriginalFirstCarrier A b ≤ zeroAt (annih (treeSpace A 8)) i := by
      rintro _ ⟨P,rfl⟩
      apply mem_zeroAt.mpr
      exact ⟨sub ⟨P,rfl⟩,by simp [d0]⟩
    have eq := Submodule.eq_of_le_of_finrank_le inc (by omega)
    rw [eq]
    exact mem_zeroAt.mpr ⟨m,by simp [d0]⟩

end
end RKResearch.Certified.ERK19
