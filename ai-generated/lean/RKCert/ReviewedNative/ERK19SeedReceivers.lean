module

public import RKCert.ReviewedNative.ERK19SeedPair

@[expose] public section

/-! # Balanced first-seed fibres earn actual clean receiver clocks -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

def activeClockSites (c v : Fin s→K) : Finset K :=
  (Finset.univ.image c).filter (fun z=>clockMass c v z≠0)

theorem clockMass_ne_of_active {c v : Fin s→K} {a : K}
    (h : a∈activeClockSites c v) : clockMass c v a≠0 := (Finset.mem_filter.mp h).2

theorem activeClockSites_in_weightedSites (c v : Fin s→K) :
    activeClockSites c v ⊆ weightedSites c v :=
  fun _ h => by
    by_contra z
    exact (Finset.mem_filter.mp h).2 (clockMass_zero_of_not_site z)

/-- The signed aggregate weights must occupy at least ten clock sites. -/
theorem order19_active_clock_count (ho : HasOrder 19 A b) :
    10≤(activeClockSites (nodes A) b).card := by
  by_contra! small
  let c := nodes A
  let T := activeClockSites c b
  change T.card<10 at small
  let H : K[X] := nodalHull T
  have hD : H.natDegree≤9 := (natDegree_nodalHull T).le.trans (by omega)
  let a : Fin 10→K := fun j=>H.coeff j.val
  have e : coeffEval A 9 a=evalNodes A H := (evalNodes_eq_coeffEval A H hD).symm
  have z (i : Fin 10) : (∑ j : Fin 10,a j/((i.val+j.val+1:ℕ):K))=0 := by
    rw [←probe_coeffEval ho (q:=9) (by have :=i.isLt; omega) a,e]
    change (∑ j, (b j * (c j)^i.val) * H.eval (c j))=0
    simp only [mul_assoc]
    rw [weighted_sum_by_clock c b (fun x=>x^i.val * H.eval x)]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases t : y∈T
    · rw [nodalHull_eval_of_mem t,mul_zero,mul_zero]
    · have z : clockMass c b y=0 := by
        by_contra live
        exact t (Finset.mem_filter.mpr ⟨hy,live⟩)
      rw [z,zero_mul]
  have vanish := moments_detect ho (n:=10) (d:=1) (by decide) (by decide)
    (fun i j => by have :=i.isLt; have :=j.isLt; omega) a z
  apply (monic_nodalHull T).ne_zero
  ext j
  rw [coeff_zero]
  by_cases v : j<10
  · exact vanish ⟨j,v⟩
  · change H.coeff j=0
    exact coeff_eq_zero_of_natDegree_lt (show H.natDegree<j by omega)

/-- A touched clock with vanishing aggregate contains two distinct
nonzero entries of the seed. -/
theorem balanced_clock_has_two {c d : Fin s→K} {x : K}
    (bal : clockMass c d x=0) :
    ∀ i, d i≠0 → c i=x → ∃ j, j≠i ∧ d j≠0 ∧ c j=x := by
  intro i di ci
  by_contra! one
  have h : clockMass c d x=d i := by
    unfold clockMass
    apply Finset.sum_eq_single_of_mem i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ci⟩)
    intro j hj ji
    by_contra jn
    exact one j ji jn ((Finset.mem_filter.mp hj).2)
  exact di (h.symm.trans bal)

/-- The individual physical seed support is at least twice its clock
support when local sums all vanish. -/
theorem balanced_support_double {c d : Fin s→K} (bal : ∀ x,clockMass c d x=0) :
    2*(weightedSites c d).card ≤
      (Finset.univ.filter (fun i=>d i≠0)).card := by
  let W := Finset.univ.filter (fun i=>d i≠0)
  let T := weightedSites c d
  have hc : W.card=∑ x ∈ T, (W.filter (fun i=>c i=x)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi=>Finset.mem_image_of_mem c hi)
  rw [hc,show 2*T.card=∑ _x ∈ T,(2:ℕ) by simp [Nat.mul_comm]]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨i,di,e⟩ := mem_weightedSites.mp hx
  obtain ⟨j,ji,dj,ej⟩ := balanced_clock_has_two (bal x) i di e
  suffices 1<(W.filter (fun i=>c i=x)).card by omega
  exact Finset.one_lt_card.mpr
    ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,dj⟩,ej⟩,
     i,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,di⟩,e⟩,ji⟩

end
end RKResearch.Certified.Graded.Reverse

namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

theorem first_carrier_zero_off {v : Fin 29→K} (hv : v∈OriginalFirstCarrier A b)
    {i : Fin 29} (d0 : firstSeed A b i=0) : v i=0 := by
  obtain ⟨P,rfl⟩ := hv
  simp [d0]

theorem first_carrier_clockMass {v : Fin 29→K} (hv : v∈OriginalFirstCarrier A b)
    (balance : ∀ x,clockMass (nodes A) (firstSeed A b) x=0) (a : K) :
    clockMass (nodes A) v a=0 := by
  obtain ⟨P,rfl⟩ := hv
  have eq : clockMass (nodes A) (weightedEval (nodes A) (firstSeed A b) P) a =
      P.eval a * clockMass (nodes A) (firstSeed A b) a := by
    rw [clockMass,clockMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [weightedEval_apply,(Finset.mem_filter.mp hi).2]
  rw [eq,balance,mul_zero]

theorem first_carrier_fibre_agreement {f : Fin 29→K}
    (hf : firstSeed A b*f∈OriginalFirstCarrier A b) {i j : Fin 29}
    (di : firstSeed A b i≠0) (dj : firstSeed A b j≠0) (same : nodes A i=nodes A j) :
    f i=f j := by
  obtain ⟨P,e⟩ := hf
  have v (k : Fin 29) (dk : firstSeed A b k≠0) :
      f k=P.eval (nodes A k) := by
    have z := congrFun e k
    exact (mul_right_inj' dk).mp (by simpa only [weightedEval_apply,Pi.mul_apply,mul_comm] using z.symm)
  rw [v i di,v j dj,same]

theorem clean_of_off_seed_live {q : ℕ} (ho : HasOrder 19 A b) (pay : q≤9)
    (band : FullFirstBand A b) (i : Fin 29) (d0 : firstSeed A b i=0) (bi : b i≠0) :
    ∀ f∈zeroSpace A q,f i=0 := by
  intro f hf
  have hc := band.represent (weight_defect_mixed_annih ho (j:=q) (k:=9) (by omega) hf)
  exact (mul_eq_zero.mp (first_carrier_zero_off hc d0 : b i*f i=0)).resolve_left bi

/-- If every live weight at this clock touches the seed and the
aggregate output there is nonzero, all touched rows at that clock are clean. -/
theorem clean_of_active_seed_clock {q : ℕ} (ho : HasOrder 19 A b) (pay : q≤9)
    (band : FullFirstBand A b) (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (trace : ∀ f∈zeroSpace A q, firstSeed A b*f∈OriginalFirstCarrier A b)
    (i : Fin 29) (di : firstSeed A b i≠0) (active : clockMass (nodes A) b (nodes A i)≠0)
    (on : ∀ j,nodes A j=nodes A i → b j≠0 → firstSeed A b j≠0) :
    ∀ f∈zeroSpace A q,f i=0 := by
  intro f hf
  have hc := band.represent (weight_defect_mixed_annih ho (j:=q) (k:=9) (by omega) hf)
  have zero := first_carrier_clockMass hc balance (nodes A i)
  have conv : clockMass (nodes A) (b*f) (nodes A i) =
      clockMass (nodes A) b (nodes A i) * f i := by
    rw [clockMass,clockMass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have same := (Finset.mem_filter.mp hj).2
    change b j*f j=b j*f i
    by_cases bj : b j=0
    · rw [bj,zero_mul,zero_mul]
    · rw [first_carrier_fibre_agreement (trace f hf) (on j same bj) di same]
  rw [conv] at zero
  exact (mul_eq_zero.mp zero).resolve_left active

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- At every nonzero-aggregate weight clock there is at least one
actual grade-nine clean stage, on or off the seed as appropriate. -/
theorem balanced_active_has_clean_nine (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (band : FullFirstBand A b) (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (split : (weightedSites (nodes A) (firstSeed A b)).card=11 ∨
      ((weightedSites (nodes A) (firstSeed A b)).card=10 ∧
       ∃i, firstSeed A b i=0 ∧ b i≠0)) {a : K} (active : a∈activeClockSites (nodes A) b) :
    ∃ i, nodes A i=a ∧ ∀f∈zeroSpace A 9,f i=0 := by
  by_cases h : ∃ i,nodes A i=a ∧ firstSeed A b i=0 ∧ b i≠0
  · obtain ⟨i,ci,d0,live⟩ := h
    exact ⟨i,ci,clean_of_off_seed_live ho le_rfl band i d0 live⟩
  have on (i : Fin 29) (ci : nodes A i=a) (bi : b i≠0) : firstSeed A b i≠0 :=
    fun z => h ⟨i,ci,z,bi⟩
  obtain ⟨i,bi,ci⟩ := mem_weightedSites.mp (activeClockSites_in_weightedSites _ _ active)
  refine ⟨i,ci,clean_of_active_seed_clock ho le_rfl band balance ?_ i (on i ci bi)
    (ci.symm ▸ clockMass_ne_of_active active) (fun j e => on j (e.trans ci))⟩
  exact fun _ hf=>balanced_grade_nine_first_trace ha ho band balance split hf

end
end RKResearch.Certified.ERK19
