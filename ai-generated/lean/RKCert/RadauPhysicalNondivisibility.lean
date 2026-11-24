module
public import RKCert.RadauRootCertificates
public import RKCert.FactorPrimitiveScale

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial RKCert.Paired RKCert.Endpoint
variable {K : Type*} [Field K] [CharZero K]

theorem degree_native_radau : (radauQuartic : K[X]).natDegree=4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have h0 : 0≠i := by omega
    have h1 : 1≠i := by omega
    have h2 : 2≠i := by omega
    have h3 : 3≠i := by omega
    have h4 : 4≠i := by omega
    simp [radauQuartic,coeff_monomial,coeff_C,Ne.symm h0,h1,h2,h3,h4]
  · simp [radauQuartic]

theorem scaled_X_radau : (X*(radauQuartic:K[X])).scaleRoots (126:K) =
    C (1:K)*((X*radauIntegral).map (Int.castRingHom K)) := by
  let : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro y
  let x := y/(126:K)
  have xy : y=126*x := by dsimp [x]; field_simp
  have hn : (radauQuartic : K[X])≠0 := by
    intro h; have hh := degree_native_radau (K:=K); rw [h,natDegree_zero] at hh; omega
  rw [xy,scaleRoots_eval_mul,natDegree_mul X_ne_zero hn,natDegree_X,degree_native_radau,
    C_1,one_mul,Polynomial.map_mul,map_X,eval_mul,eval_X,eval_mul,eval_X,scaled_radau_eval]
  ring

theorem checked_radau_factors : checked 12 2 (0::radauKnots) radauKnots=true := by decide +kernel

theorem radau_divisor_first_moment {P : K[X]} {u : K} (hdiv : P∣ X*radauQuartic)
    (hd : P.natDegree≤2) (hu : u≠0) (root : radauQuartic.eval u=0) :
    (primitive (X*P)).eval u≠0 := by
  have G0 : X*(radauQuartic:K[X])≠0 := by
    apply mul_ne_zero X_ne_zero
    intro h; have hh:=degree_native_radau (K:=K); rw [h,natDegree_zero] at hh; omega
  apply native_from_scaled _ radauIntegral (126:K) 1 (by norm_num) one_ne_zero
    scaled_X_radau 12 2 (by intro i hi; interval_cases i <;> decide) _
    P u (ne_zero_of_dvd_ne_zero G0 hdiv) hdiv hd hu (by rw [eval_mul,root,mul_zero])
  exact good_prime 191 (X*radauIntegral) radauIntegral (monic_X.mul monic_radau_integral)
    monic_radau_integral 12 2 (modular_table _ _ 12 2 (0::radauKnots) radauKnots
      (splitX _ _ split_radau191) split_radau191 checked_radau_factors)

/-- At the earliest nonzero clean stage, the actual strict lower tableau
forces J(XP)(u)=0 for any quadratic-or-lower head fitting all off rows. -/
theorem first_nonzero_clean_test {s:ℕ} {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (P : K[X]) (hd : P.natDegree≤2)
    (off : ∀i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hex : ∃i, qdef A i=0 ∧ nodes A i≠0) :
    ∃u∈onNodes A, u≠0 ∧ (primitive (X*P)).eval u=0 := by
  let U : Set (Fin s) := {i | qdef A i=0 ∧ nodes A i≠0}
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U (show U.Nonempty from hex)
  obtain ⟨di,ni⟩ := (show qdef A i=0 ∧ nodes A i≠0 from hi)
  refine ⟨nodes A i,mem_onNodes.mpr ⟨i,di,rfl⟩,ni,?_⟩
  apply on_primitive_zero_of_prefix ha hF di (X*P) (natDegree_mul_le_of_le (by simp) hd)
    (diag (nodes A) (qdef A)) (on_row_quartic_conditions hF di).2.2
  intro j hj
  by_cases dj : qdef A j=0
  · have nj : nodes A j=0 := by by_contra ne; exact hmin j ⟨dj,ne⟩ hj
    simp [nj,dj]
  · simp [off j dj]

/-- Actual order-nine five-on-node profile: even a linear nonzero head cannot
divide the on-node hull. The statement needs only the displayed physical
grade-four chain and aggregate off-weight conditions, not chronological
separation of stage rows or a real ordering. -/
theorem order9_five_on_head_not_dvd {s:ℕ} {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) (hM : (onNodes A).card=5)
    (hOffWeights : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2) (P : K[X]) (hd : P.natDegree≤2)
    (off : ∀i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) : ¬ P∣nodalHull (onNodes A) := by
  have rad := order9_nodal_radau ha ho hM hOffWeights
  obtain ⟨u,hu,nu,test⟩:=first_nonzero_clean_test ha hF P hd off
    (exists_nonzero_on_of_card (by omega))
  intro div
  rw [nodalHull_erase_factor _ (zero_mem_onNodes ha),rad,map_zero,sub_zero] at div
  exact radau_divisor_first_moment div hd nu (radau_on_root rad hu nu) test

end RKCert.FixedFactor
