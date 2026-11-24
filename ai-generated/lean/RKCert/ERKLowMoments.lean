module

public import RKCert.ERKLowCurves

@[expose] public section

/-! # Low-order two-curve aggregation and exact scalar moment budgets -/
namespace RKCert.Paired
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem defect_polynomial_pair_zero {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {j k : ℕ} (hpay : j+k+1 ≤ p)
    {d : Vec K s} (hd : d∈zeroSpace A j) (P : Polynomial K) (hp : P.natDegree ≤ k) :
    row b (diag (evalNodes A P) d) = 0 := by
  have he : diag (evalNodes A P) d = diag d (polyEval A k (fun i => P.coeff i.val)) := by
    rw [evalNodes_eq_polyEval A P hp]
    ext i; simp [mul_comm]
  rw [he,polyEval_apply,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul,map_smul]
  have h : row b (diag d (normTree A (Tree.bush i.val))) = probe A b i.val d := by
    simp only [normTree_bush,row_apply,diag_apply,probe]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h,probe_zeroSpace ho (by omega : i.val+j+1 ≤ p) hd,smul_zero]

/-- Total output weight at an off feature, not the weight of an individual
stage and not the aggregate of a possible on feature at the same abscissa. -/
noncomputable def offWeight (A : Fin s → Fin s → K) (b : Vec K s) (x : K) : K :=
  ∑ i, if qdef A i≠0 ∧ nodes A i=x then b i else 0

/-- Exactly the degree budget in the order-nine manuscript: seven off
knots at p=9, or six at p=8, permit the full aggregate cancellation. -/
theorem offWeight_eq_zero_from_head {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (P : Polynomial K)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hb : (supportedNodes A (qdef A)).card+2 ≤ p) (x : K)
    (hx : x∈supportedNodes A (qdef A)) : offWeight A b x=0 := by
  let S := supportedNodes A (qdef A)
  change S.card+2 ≤ p at hb
  let f : K → K := fun y => if y=x then 1 else 0
  let Q := Lagrange.interpolate S id f
  have he (y : K) (hy : y∈S) : Q.eval y=f y :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hy
  have hQ : Q.natDegree < S.card := by
    by_cases h : Q=0
    · rw [h,Polynomial.natDegree_zero]
      exact Finset.card_pos.mpr ⟨x,hx⟩
    · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr
        (Lagrange.degree_interpolate_lt f (Set.injOn_id _))
  have hz := defect_polynomial_pair_zero ho (by omega : 2+Q.natDegree+1 ≤ p)
    (qdef_mem A) Q le_rfl
  have hvalue : row b (diag (evalNodes A Q) (qdef A)) = P.eval x * offWeight A b x := by
    simp only [row_apply,diag_apply,evalNodes_apply,offWeight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hd : qdef A i=0
    · simp [hd]
    · have hmi : nodes A i∈S := mem_supportedNodes.mpr ⟨i,hd,rfl⟩
      rw [he _ hmi]
      by_cases hn : nodes A i=x
      · have hQ := hP i hd
        rw [hn] at hQ
        simp [hd,hn,f,hQ,mul_comm]
      · simp [hd,hn,f]
  have hPn : P.eval x≠0 := by
    obtain ⟨i,hi,hx'⟩ := mem_supportedNodes.mp hx
    rwa [← hx',hP i hi]
  rw [hvalue] at hz
  exact (mul_eq_zero.mp hz).resolve_left hPn

noncomputable def onNodes (A : Fin s → Fin s → K) : Finset K :=
  (Finset.univ.filter fun i => qdef A i=0).image (nodes A)

omit [CharZero K] in
theorem mem_onNodes {A : Fin s → Fin s → K} {x : K} :
    x∈onNodes A ↔ ∃ i : Fin s, qdef A i=0 ∧ nodes A i=x := by
  simp [onNodes,Finset.mem_filter,Finset.mem_image]

theorem zero_mem_onNodes {A : Fin (s+1) → Fin (s+1) → K} (ha : StrictLower A) :
    0∈onNodes A := by
  apply mem_onNodes.mpr
  refine ⟨0,origin_zeroSpace A ha 2 (qdef_mem A),?_⟩
  unfold nodes
  exact Finset.sum_eq_zero fun j _ => ha 0 j (Nat.zero_le _)

omit [CharZero K] in
/-- Any polynomial vanishing on the on features has all affordable
monomial probes zero once off output aggregates have been proved zero. -/
theorem probes_zero_of_on_roots {A : Fin s → Fin s → K} {b : Vec K s}
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0)
    (P : Polynomial K) (hP : ∀ x∈onNodes A, P.eval x=0) (k : ℕ) :
    probe A b k (evalNodes A P)=0 := by
  let T : Finset K := supportedNodes A (qdef A)
  have hsplit (i : Fin s) : b i * nodes A i^k * P.eval (nodes A i) =
      ∑ x∈T, (if qdef A i≠0 ∧ nodes A i=x then b i else 0) * (x^k*P.eval x) := by
    by_cases hi : qdef A i=0
    · have hV := hP _ (mem_onNodes.mpr ⟨i,hi,rfl⟩)
      simp [hi,hV]
    · have hm : nodes A i∈T := mem_supportedNodes.mpr ⟨i,hi,rfl⟩
      rw [Finset.sum_eq_single (nodes A i)]
      · simp only [hi,ne_eq,not_false_eq_true,and_true,ite_true]
        ring
      · intro x _ hx
        simp [Ne.symm hx]
      · intro hx; exact False.elim (hx hm)
  simp only [probe,row_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i),Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x hx
  rw [← Finset.sum_mul]
  change offWeight A b x * (x^k * P.eval x)=0
  rw [hoff x hx,zero_mul]

omit [CharZero K] in
/-- The first zero node saves precisely the moment needed at even order
eight. This uses a complete shifted Cauchy system, not positivity. -/
theorem zero_of_anchored_profile_probes {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (q : ℕ) (hp : 2*q ≤ p)
    (P : Polynomial K) (hd : P.natDegree ≤ q) (h0 : P.eval 0=0)
    (hm : ∀ k : Fin q, probe A b k.val (evalNodes A P)=0) : P=0 := by
  let a : Fin q → K := fun j => P.coeff (j.val+1)
  have hc : P.coeff 0=0 := by rw [Polynomial.coeff_zero_eq_eval_zero,h0]
  have hs (i : Fin q) : (∑ j : Fin q, a j / ((i.val+j.val+2:ℕ):K))=0 := by
    have h := hm i
    rw [evalNodes_eq_polyEval A P hd,probe_polyEval ho (by omega),Fin.sum_univ_succ] at h
    simpa only [Fin.val_zero,hc,zero_div,zero_add,Fin.val_succ,Nat.add_assoc,a] using h
  have ha := moments_detect ho (d:=2) (by decide) (by omega) (fun i j => by omega) a hs
  ext k
  simp only [Polynomial.coeff_zero]
  by_cases he : k=0
  · rwa [he]
  · by_cases h : k ≤ q
    · let i : Fin q := ⟨k-1,by omega⟩
      have haux : i.val+1=k := by dsimp [i]; omega
      simpa only [a,haux] using ha i
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- If off weights cancel and a first zero node is present, both p=8
and p=9 already require at least five distinct on nodes. -/
theorem five_on_of_aggregate_zero {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 8 ≤ p)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    5 ≤ (onNodes A).card := by
  by_contra! hn
  let T := onNodes A
  let P : Polynomial K := ∏ x∈T, (X-C x)
  have hm : P.Monic := Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C x)
  have hdeg : P.natDegree ≤ 4 := by
    have hEq : P.natDegree=T.card := by simp [P]
    change T.card < 5 at hn
    omega
  have hroots (x : K) (hx : x∈T) : P.eval x=0 := by
    rw [show P.eval x = ∏ y∈T, (X-C y : Polynomial K).eval x by simp [P,Polynomial.eval_prod]]
    exact Finset.prod_eq_zero hx (by simp)
  have h0 := hroots 0 (zero_mem_onNodes ha)
  have hz : P=0 := zero_of_anchored_profile_probes ho 4 (by omega) P hdeg h0
    (fun i => probes_zero_of_on_roots hoff P hroots i.val)
  exact hm.ne_zero hz

end RKCert.Paired
