module

public import RKCert.ReviewedNative.ERK19FiniteSeedExclusion

@[expose] public section

/-! # Exact bounded polynomial traces on the actual first-seed support -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

theorem weighted_eq_at_enough_sites {c d : Fin s→K} {P Q : K[X]} {j : ℕ}
    (wide : j < (weightedSites c d).card) (dp : P.natDegree≤j) (dq : Q.natDegree≤j)
    (equal : weightedEval c d P=weightedEval c d Q) : P=Q := by
  apply sub_eq_zero.mp
  have deg : (P-Q).natDegree≤j := by simpa only [max_self] using natDegree_sub_le_of_le dp dq
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (weightedSites c d)
  · exact (degree_le_natDegree.trans (by exact_mod_cast deg)).trans_lt
      (by exact_mod_cast wide : (j : WithBot ℕ) < ((weightedSites c d).card : WithBot ℕ))
  · intro a ha
    obtain ⟨i,di,ci⟩ := mem_weightedSites.mp ha
    have e := congrFun equal i
    simp only [weightedEval_apply,ci] at e
    rw [eval_sub, (mul_left_inj' di).mp e,sub_self]

theorem original_first_degree_eight_trace (ho : HasOrder 19 A b) (band : FullFirstBand A b)
    {v : Fin 29→K} (hv : v∈treeSpace A 8) :
    ∃P : K[X], P.natDegree≤8 ∧ weightedEval (nodes A) (firstSeed A b) P=firstSeed A b*v := by
  have h := first_seed_mixed_annih ho (j:=8) (k:=9) (by decide) hv
  rw [band] at h
  obtain ⟨Q,dQ,eq⟩ := mem_weightedBand.mp h
  have deg : Q.natDegree≤8 := by
    by_cases z : Q=0
    · simp [z]
    · have lt := (natDegree_lt_iff_degree_lt z).mpr dQ
      omega
  let S := (1-X : K[X])
  have Sdeg : S.natDegree≤1 := by
    change (1-X : K[X]).natDegree ≤ 1
    exact (natDegree_sub_le _ _).trans (by simp)
  refine ⟨Q.comp S,natDegree_comp_le.trans ((Nat.mul_le_mul deg Sdeg).trans_eq (Nat.mul_one 8)),?_⟩
  ext i
  have e := congrFun eq i
  simpa only [S,weightedEval_apply,eval_comp,eval_sub,eval_one,eval_X,reflectedClock,
    Pi.sub_apply,Pi.one_apply] using e

theorem clock_pow_mem_invariant {c : Fin s→K} {U : Submodule K (Fin s→K)}
    (stable : U.map (diag c)≤U) {v : Fin s→K} (hv : v∈U) (k : ℕ) :
    (diag c^k) v∈U := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact stable (Submodule.mem_map_of_mem ih)

theorem clock_pow_mem_new_grade {v : Fin 29→K} {j : ℕ}
    (hv : v∈zeroSpace A j) (k : ℕ) : (diag (nodes A)^k) v∈zeroSpace A (j+k) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    change _∈zeroSpace A (j+k+1)
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact diag_zeroSpace A _ ih

theorem clock_pow_matches_trace {c d v : Fin s→K} {P : K[X]}
    (eq : weightedEval c d P=d*v) (k : ℕ) :
    weightedEval c d (X^k*P)=d*((diag c^k) v) := by
  ext i
  have h := congrFun eq i
  simp only [weightedEval_apply,Pi.mul_apply] at h
  simp only [weightedEval_apply,eval_mul,eval_pow,eval_X,Pi.mul_apply,HeadFiber.clock_power_value]
  rw [mul_assoc (c i ^ k), h]
  ring

theorem trace_degree_from_paid_shift (ho : HasOrder 19 A b) (band : FullFirstBand A b)
    (wide : 19≤(weightedSites (nodes A) (firstSeed A b)).card)
    {v : Fin 29→K} {P : K[X]} (pNZ : P≠0) (dP : P.natDegree≤8)
    (trace : weightedEval (nodes A) (firstSeed A b) P=firstSeed A b*v)
    {k : ℕ} (kpay : k≤9) (paid : (diag (nodes A)^k) v∈zeroSpace A 8) :
    k+P.natDegree≤8 := by
  obtain ⟨Q,dQ,eq⟩ := original_first_degree_eight_trace ho band (zeroSpace_le_treeSpace A 8 paid)
  have deg : (X^k*P).natDegree=k+P.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) pNZ,natDegree_X_pow]
  have same := weighted_eq_at_enough_sites (j:=18) (by omega)
    (show (X^k*P).natDegree≤18 by rw [deg];omega) (dQ.trans (by decide))
    ((clock_pow_matches_trace trace k).trans eq.symm)
  rwa [←deg,same]

/-- Poly lift using coefficients through n rather than its unreduced
syntax, so a purchased power is never charged twice. -/
theorem weighted_mem_paid_chain {c w : Fin s→K} {U : Submodule K (Fin s→K)}
    {n : ℕ} (P : K[X]) (degree : P.natDegree<n) :
    weightedEval c w P∈chain (diag c) U w n := by
  have paid := (clock_chain_le_iff (T:=diag c) (U:=U) (w:=w) n).mp le_rfl
  rw [P.as_sum_range' n degree,map_sum]
  apply Submodule.sum_mem
  intro j hj
  have e : weightedEval c w (monomial j (P.coeff j)) = (P.coeff j) • (diag c^j) w := by
    ext i
    simp [mul_assoc]
  rw [e]
  exact Submodule.smul_mem _ _ (paid.2 j (Finset.mem_range.mp hj))

theorem eval_alias_from_full_probes {q : ℕ} (ho : HasOrder 19 A b)
    (pay : 2*q+1≤19) {v : Fin 29→K} (hv : v∈treeSpace A q)
    (probeZero : ∀ i : Fin (q+1),probe A b i.val v=0) : v∈zeroSpace A q := by
  rw [treeSpace_coeff_sup ho (by omega)] at hv
  obtain ⟨_,⟨a,rfl⟩,u,hu,rfl⟩ := Submodule.mem_sup.mp hv
  have c (i : Fin (q+1)) : (∑ j : Fin (q+1), a j/((i.val+j.val+1:ℕ):K))=0 := by
    have h := probeZero i
    have z : probe A b i.val u=0 := probe_zeroSpace ho (by have :=i.isLt;omega) hu
    rw [map_add,z,add_zero,probe_coeffEval ho (by have :=i.isLt;omega)] at h
    exact h
  have h := moments_detect ho (n:=q+1) (d:=1) (by decide) (by omega)
    (fun i j=>by have :=i.isLt;have :=j.isLt;omega) a c
  have az : a=0 := funext h
  rw [az,map_zero,zero_add]
  exact hu

end
end RKResearch.Certified.ERK19
