module

public import RKCert.ERKLowEndpointCore

@[expose] public section

/-! # Actual order-eight Lobatto exclusions

The arguments use only the genuine terminal column, the checked midpoint
chart, and the primitive tests at chronological clean rows.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem nodalHull_erase_factor (T : Finset K) {a : K} (ha : a∈T) :
    nodalHull T = (X-C a)*nodalHull (T.erase a) := by
  unfold nodalHull
  exact (Finset.mul_prod_erase T _ ha).symm

omit [CharZero K] in
theorem nodalHull_two_endpoint_factor (T : Finset K) (h0 : (0:K)∈T) (h1 : (1:K)∈T) :
    nodalHull T = (X^2-X)*nodalHull ((T.erase 1).erase 0) := by
  rw [nodalHull_erase_factor T h1,nodalHull_erase_factor (T.erase 1)
    (Finset.mem_erase.mpr ⟨zero_ne_one,h0⟩)]
  simp only [map_one,map_zero,sub_zero]
  ring

omit [CharZero K] in
theorem nodalHull_eval_ne_zero_of_notMem {T : Finset K} {u : K} (hu : u∉T) :
    (nodalHull T).eval u≠0 := by
  simp only [nodalHull,eval_prod,eval_sub,eval_X,eval_C]
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (fun h => hu (h.symm ▸ ha)))

theorem treeSpace_four_profile {A : Fin s → Fin s → K} {v : Vec K s}
    (hv : v∈treeSpace A 4) (hF : zeroSpace A 4=chainSpan A (qdef A) 2) :
    ∃ Q R : K[X], Q.natDegree ≤ 4 ∧ R.natDegree ≤ 2 ∧
      evalNodes A Q + diag (qdef A) (evalNodes A R) = v := by
  obtain ⟨Q,hQ,hw⟩ := exists_poly_zeroSpace_charZero A hv
  rw [hF,chainSpan_iff_polynomial] at hw
  obtain ⟨R,hR,he⟩ := hw
  refine ⟨Q,R,hQ,hR,?_⟩
  rw [←he]
  abel

omit [CharZero K] in
theorem profile_on_eval {A : Fin s → Fin s → K} (Q R : K[X]) {v : Vec K s}
    (hv : evalNodes A Q + diag (qdef A) (evalNodes A R)=v) {i : Fin s}
    (hi : qdef A i=0) : Q.eval (nodes A i)=v i := by
  simpa [hi] using congrFun hv i

omit [CharZero K] in
theorem profile_off_eval {A : Fin s → Fin s → K} {P Q R : K[X]} {v : Vec K s}
    (hv : evalNodes A Q + diag (qdef A) (evalNodes A R)=v)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    {i : Fin s} (hi : qdef A i≠0) : (Q+P*R).eval (nodes A i)=v i := by
  simpa [hP i hi] using congrFun hv i

omit [CharZero K] in
theorem single_profile_on_unique {A : Fin (s+1) → Fin (s+1) → K} {Q R : K[X]}
    (he : evalNodes A Q + diag (qdef A) (evalNodes A R) = Pi.single (Fin.last s) 1)
    (hdi : qdef A (Fin.last s)=0) (hc : nodes A (Fin.last s)=1) (j : Fin (s+1))
    (hj : qdef A j=0) (h1 : nodes A j=1) : j=Fin.last s := by
  by_contra hne
  have h := (profile_on_eval Q R he hj).symm.trans ((congrArg (fun x => Q.eval x)
    (h1.trans hc.symm)).trans (profile_on_eval Q R he hdi))
  simp [hne] at h

theorem terminal_on_of_six_off {A : Fin (s+1) → Fin (s+1) → K} {P Q R : K[X]}
    (hv : evalNodes A Q + diag (qdef A) (evalNodes A R) = Pi.single (Fin.last s) 1)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hPd : P.natDegree ≤ 2) (hQd : Q.natDegree ≤ 4) (hRd : R.natDegree ≤ 2)
    (hN : 6 ≤ (supportedNodes A (qdef A)).card) : qdef A (Fin.last s)=0 := by
  by_contra hf
  let i := Fin.last s
  let T := (supportedNodes A (qdef A)).erase (nodes A i)
  have hc : T.card+1=(supportedNodes A (qdef A)).card :=
    Finset.card_erase_add_one (mem_supportedNodes.mpr ⟨i,hf,rfl⟩)
  have hd : (Q+P*R).natDegree ≤ 4 := Polynomial.natDegree_add_le_of_degree_le hQd
    (Polynomial.natDegree_mul_le_of_le hPd hRd)
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (Q+P*R) T (fun x hx => by
    obtain ⟨hxc,hxs⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,hc⟩ := mem_supportedNodes.mp hxs
    have hji : j≠i := fun h => hxc (hc.symm.trans (congrArg (nodes A) h))
    rw [←hc,profile_off_eval hv hP hj]
    simp [hji,i]) (by omega)
  have h := profile_off_eval hv hP hf
  simp [hz] at h

theorem beta_cubic_from_actual_probes {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (hp : 8 ≤ p) (Q : K[X]) (hd : Q.natDegree ≤ 3)
    (hz : ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*Q))=0) :
    Q = C (Q.coeff 3)*lobattoCubic := by
  apply lobatto_cubic_decoder Q hd
  intro k
  exact beta_probe_coeff ho Q hd (by have := k.isLt; omega) (hz k)

theorem order8_nodal_lobatto {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8)
    (hM : (onNodes A).card=5) (h1 : (1:K)∈onNodes A)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    nodalHull (((onNodes A).erase 1).erase 0) = lobattoCubic := by
  let S := ((onNodes A).erase 1).erase 0
  let H := nodalHull S
  have h0 := zero_mem_onNodes ha
  have hc1 := Finset.card_erase_add_one h1
  have hc0 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨zero_ne_one,h0⟩ :
    (0:K)∈(onNodes A).erase 1)
  change S.card+1=((onNodes A).erase 1).card at hc0
  have hd : H.natDegree=3 := by
    change (nodalHull S).natDegree=3
    rw [natDegree_nodalHull]
    omega
  have he : H = C (H.coeff 3)*lobattoCubic := beta_cubic_from_actual_probes ho (by decide)
    H hd.le (fun i => by
      rw [← nodalHull_two_endpoint_factor (onNodes A) h0 h1]
      exact probes_zero_of_on_roots hoff _ (fun _ => nodalHull_eval_of_mem) i.val)
  have hC : H.coeff 3=1 := hd ▸ (monic_nodalHull S).coeff_natDegree
  simpa [hC] using he

omit [CharZero K] in
theorem on_root_or_endpoints {A : Fin s → Fin s → K}
    (hS : nodalHull (((onNodes A).erase 1).erase 0)=lobattoCubic) :
    ∀ x∈onNodes A, x=0 ∨ x=1 ∨ lobattoCubic.eval x=0 := by
  intro x hx
  by_cases h0 : x=0
  · exact Or.inl h0
  by_cases h1 : x=1
  · exact Or.inr (Or.inl h1)
  exact Or.inr (Or.inr (hS ▸ nodalHull_eval_of_mem
    (Finset.mem_erase.mpr ⟨h0,Finset.mem_erase.mpr ⟨h1,hx⟩⟩)))

/-- Exact chronological obstruction for the last factor of a Lobatto
chart: every earlier on row is at zero or at a root of the quadratic. -/
theorem lobatto_physical_factor_impossible {A : Fin (s+1) → Fin (s+1) → K}
    (ha : StrictLower A) (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : K[X]} (hPd : P.natDegree ≤ 2)
    (hP : ∀ j, qdef A j≠0 → P.eval (nodes A j)=qdef A j)
    (hUnique : ∀ j, qdef A j=0 → nodes A j=1 → j=Fin.last s)
    (hOn : ∀ x∈onNodes A, x=0 ∨ x=1 ∨ lobattoCubic.eval x=0)
    {u a : K} (hu : u∈onNodes A) (ha0 : a≠0)
    (hfac : lobattoCubic = (X-C u)*(C a*P)) : False := by
  have hRoot := lobatto_isRoot_of_linear hfac
  have hu0 : u≠0 := by
    intro h
    rw [h] at hRoot
    norm_num [lobattoCubic] at hRoot
  let U : Set (Fin (s+1)) := {j | qdef A j=0 ∧ nodes A j=u}
  have hU : U.Nonempty := mem_onNodes.mp hu
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  rcases (show qdef A i=0 ∧ nodes A i=u from hi) with ⟨hdi,hci⟩
  have hpre (j : Fin (s+1)) (hj : j < i) (hdj : qdef A j=0) :
      nodes A j=0 ∨ P.eval (nodes A j)=0 := by
    have hne : nodes A j≠u := fun hj' => hmin j ⟨hdj,hj'⟩ hj
    rcases hOn _ (mem_onNodes.mpr ⟨j,hdj,rfl⟩) with h0|h1|hr
    · exact Or.inl h0
    · exact False.elim ((ne_of_lt (hj.trans_le (Fin.le_last i))) (hUnique j hdj h1))
    · rw [hfac,eval_mul,eval_mul,eval_C,eval_sub,eval_X,eval_C] at hr
      exact Or.inr ((mul_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr hne))).resolve_left ha0)
  have hdeg : (C a*P).natDegree ≤ 2 := (natDegree_C_mul_le _ _).trans hPd
  have hX : (X*(C a*P)).natDegree ≤ 3 := natDegree_mul_le_of_le (by simp) hdeg
  have hAC := (on_row_quartic_conditions hF hdi).2.2
  have hv : mat A (a • diag (nodes A) (qdef A)) i = 0 := by
    rw [map_smul,Pi.smul_apply,hAC,smul_zero]
  have hp := on_primitive_zero_of_prefix ha hF hdi _ hX _ hv (fun j hj => by
    by_cases hG : qdef A j=0
    · rcases hpre j hj hG with h|h <;> simp [hG,h]
    · simp [hP j hG,mul_left_comm])
  rw [hci] at hp
  exact lobatto_first_on_scalar_gate hdeg hu0 hfac hp

theorem lobattoCubic_degree : (lobattoCubic : K[X]).natDegree=3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hi0 : 0≠i := by omega
    have hi1 : 1≠i := by omega
    have hi2 : 2≠i := by omega
    have hi3 : 3≠i := by omega
    simp [lobattoCubic,coeff_monomial,coeff_C,Ne.symm hi0,hi1,hi2,hi3]
  · simp [lobattoCubic,coeff_monomial]

/-- A quadratic divisor of the fixed cubic leaves one exact linear
factor, with no ordering on roots needed. -/
theorem lobatto_divisor_linear_factor {P : K[X]} (hd : P.natDegree=2)
    (hdiv : P∣lobattoCubic) :
    ∃ u a : K, a≠0 ∧ lobattoCubic = (X-C u)*(C a*P) := by
  obtain ⟨R,he⟩ := hdiv
  have hn : (lobattoCubic : K[X])≠0 := by
    intro h; have hd := lobattoCubic_degree (K:=K); simp [h] at hd
  have hR : R≠0 := by intro h; apply hn; simp [he,h]
  have hP : P≠0 := by intro h; apply hn; simp [he,h]
  have hdeg := natDegree_mul hP hR
  rw [←he,lobattoCubic_degree,hd] at hdeg
  obtain ⟨a,ha,b,hb⟩ := Polynomial.natDegree_eq_one.mp (by omega : R.natDegree=1)
  let u := -b/a
  have hconst : -(a*u)=b := by
    dsimp [u]
    field_simp [ha]
  have hR' : R=(X-C u)*C a := by
    rw [←hb,sub_mul,mul_comm X,←map_mul,mul_comm u a,sub_eq_add_neg,← map_neg,hconst]
  exact ⟨u,a,ha,by rw [he,hR']; ring⟩

/-- Off cancellation is not needed for the product-of-curves argument:
the true defect probes pay exactly the degree of the on polynomial. -/
theorem on_hull_times_head_probes {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {P : K[X]}
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (k : ℕ) (hpay : k+(onNodes A).card+3 ≤ p) :
    probe A b k (evalNodes A (P*nodalHull (onNodes A)))=0 := by
  let H := nodalHull (onNodes A)
  have hd : H.natDegree=(onNodes A).card := natDegree_nodalHull _
  have he : evalNodes A (P*H)=diag (evalNodes A H) (qdef A) := by
    ext i
    by_cases hi : qdef A i=0
    · have hz : H.eval (nodes A i)=0 := nodalHull_eval_of_mem (mem_onNodes.mpr ⟨i,hi,rfl⟩)
      simp [hi,hz]
    · simp [hP i hi,mul_comm]
  rw [he]
  have hz (j : ℕ) : signal A (qdef A) j∈zeroSpace A (2+j) :=
    chainSpan_le_zeroSpace (qdef_mem A) j (signal_mem_chainSpan A _ le_rfl)
  have he' : probe A b k (diag (evalNodes A H) (qdef A)) =
      row b (diag (evalNodes A H) (signal A (qdef A) k)) := by
    simp only [probe,row_apply,diag_apply,signal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he']
  exact defect_polynomial_pair_zero ho (by omega) (hz k) H le_rfl

end RKCert.Paired

