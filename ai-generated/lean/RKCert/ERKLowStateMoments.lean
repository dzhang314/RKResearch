module

public import RKCert.ERKOrderNineRadau

@[expose] public section

/-! # Aggregating the genuine state-valued moment tests -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] {s p : ℕ}

noncomputable def onWeight (A : Fin s → Fin s → K) (b : Vec K s) (x : K) : K :=
  ∑ i, if qdef A i=0 ∧ nodes A i=x then b i else 0

theorem sum_tagged_fibers (b : Vec K s) (c : Vec K s) (tag : Fin s → Prop) [DecidablePred tag] (f : K → K) :
    (∑ i, if tag i then b i*f (c i) else 0) =
      ∑ x∈(Finset.univ.filter tag).image c, (∑ i, if tag i ∧ c i=x then b i else 0)*f x := by
  let S := (Finset.univ.filter tag).image c
  have he (i : Fin s) :
      (if tag i then b i*f (c i) else 0) =
        ∑ x∈S, (if tag i ∧ c i=x then b i else 0)*f x := by
    by_cases h : tag i
    · have hS : c i∈S := Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
      rw [Finset.sum_eq_single (c i)]
      · simp [h]
      · intro x _ hx; simp [Ne.symm hx]
      · intro hn; exact False.elim (hn hS)
    · simp [h]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.sum_mul ..).symm

/-- Exact scalar quadrature on the on-node fibers, after cancellation
of the off output weights; no sign or simplicity assumption is needed. -/
theorem probe_eq_on_weights {A : Fin s → Fin s → K} {b : Vec K s}
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0)
    (P : K[X]) (k : ℕ) :
    probe A b k (evalNodes A P) = ∑ x∈onNodes A, onWeight A b x * (x^k*P.eval x) := by
  let f (x : K) := x^k*P.eval x
  have he (i : Fin s) : b i*nodes A i^k*P.eval (nodes A i) =
      (if qdef A i=0 then b i*f (nodes A i) else 0) +
      (if qdef A i≠0 then b i*f (nodes A i) else 0) := by
    by_cases h : qdef A i=0 <;> simp [h,f,mul_assoc]
  simp only [probe,row_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib,
    sum_tagged_fibers b (nodes A) (fun i => qdef A i=0) f,
    sum_tagged_fibers b (nodes A) (fun i => qdef A i≠0) f]
  change _ + (∑ x∈supportedNodes A (qdef A), offWeight A b x * f x) = _
  have hOff : (∑ x∈supportedNodes A (qdef A), offWeight A b x * f x)=0 :=
    Finset.sum_eq_zero (fun x hx => by rw [hoff x hx,zero_mul])
  rw [hOff,add_zero]
  rfl

/-- Polynomial moment injectivity without the origin hypothesis. -/
theorem zero_of_full_profile_probes {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (q : ℕ) (hp : 2*q+1 ≤ p)
    (P : K[X]) (hd : P.natDegree ≤ q)
    (hm : ∀ i : Fin (q+1), probe A b i.val (evalNodes A P)=0) : P=0 := by
  let a : Fin (q+1) → K := fun j => P.coeff j.val
  have hs (i : Fin (q+1)) : (∑ j : Fin (q+1), a j / ((i.val+j.val+1:ℕ):K))=0 := by
    have h := hm i
    rwa [evalNodes_eq_polyEval A P hd,probe_polyEval ho (by omega)] at h
  have hz := moments_detect ho (d:=1) (by decide) (by omega) (fun i j => by omega) a hs
  ext n
  by_cases h : n < q+1
  · exact hz ⟨n,h⟩
  · simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n))

theorem order9_five_on_weights_nonzero {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b 9) (hM : (onNodes A).card=5)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0)
    {x : K} (hx : x∈onNodes A) : onWeight A b x≠0 := by
  intro hz
  let S := (onNodes A).erase x
  let Q := nodalHull S
  have hc : S.card+1=(onNodes A).card := Finset.card_erase_add_one hx
  have hd : Q.natDegree≤4 := by rw [show Q.natDegree=S.card from natDegree_nodalHull _]; omega
  have hMom (i : Fin 5) : probe A b i.val (evalNodes A Q)=0 := by
    rw [probe_eq_on_weights hoff]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases he : y=x
    · simp [he,hz]
    · rw [nodalHull_eval_of_mem (show y∈S from Finset.mem_erase.mpr ⟨he,hy⟩),mul_zero,mul_zero]
  exact (monic_nodalHull S).ne_zero (zero_of_full_profile_probes ho 4 (by decide) Q hd hMom)

noncomputable def extendFeature (T : Finset K) (z : T → K) (x : K) : K :=
  if h : x∈T then z ⟨x,h⟩ else 0

theorem extendFeature_mem (T : Finset K) (z : T → K) {x : K} (hx : x∈T) :
    extendFeature T z x=z ⟨x,hx⟩ := dite_eq_left hx

theorem row_onOff_eval_eq_onWeights {A : Fin s → Fin s → K} {b : Vec K s}
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0)
    (z : (onNodes A → K) × (supportedNodes A (qdef A) → K)) (P : K[X]) :
    row b (diag (evalNodes A P) (onOffEval A z)) =
      ∑ x∈onNodes A, onWeight A b x * (P.eval x*extendFeature (onNodes A) z.1 x) := by
  let S := supportedNodes A (qdef A)
  let T := onNodes A
  let f (x : K) := P.eval x * extendFeature T z.1 x
  let g (x : K) := P.eval x * extendFeature S z.2 x
  have he (i : Fin s) : b i*(P.eval (nodes A i)*onOffEval A z i) =
      (if qdef A i=0 then b i*f (nodes A i) else 0) +
      (if qdef A i≠0 then b i*g (nodes A i) else 0) := by
    by_cases h : qdef A i=0
    · rw [onOffEval_on A _ h]
      simp [h,f,extendFeature_mem T z.1 (mem_onNodes.mpr ⟨i,h,rfl⟩)]
    · rw [onOffEval_off A _ h]
      simp [h,g,extendFeature_mem S z.2 (mem_supportedNodes.mpr ⟨i,h,rfl⟩)]
  simp only [row_apply,diag_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib,
    sum_tagged_fibers b (nodes A) (fun i => qdef A i=0) f,
    sum_tagged_fibers b (nodes A) (fun i => qdef A i≠0) g]
  change _ + (∑ x∈S, offWeight A b x * g x) = _
  have hOff : (∑ x∈S, offWeight A b x * g x)=0 :=
    Finset.sum_eq_zero (fun x hx => by rw [hoff x hx,zero_mul])
  rw [hOff,add_zero]
  rfl

/-- Only after actual E5 is state-valued can the four nonzero on-node
moment equations turn every fifth-grade defect into an on-row zero. -/
theorem state_defect_five_zero_on [CharZero K] {A : Fin (s+1) → Fin (s+1) → K}
    {b : Vec K (s+1)} (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=5)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0)
    {v : Vec K (s+1)} (hv : v∈zeroSpace A 5) (hstate : v∈onOffSpace A)
    {i : Fin (s+1)} (hi : qdef A i=0) : v i=0 := by
  obtain ⟨z,rfl⟩ := hstate
  let T := onNodes A
  let S := T.erase 0
  let f := extendFeature T z.1
  have hD0 : qdef A (0 : Fin (s+1))=0 := origin_zeroSpace A ha 2 (qdef_mem A)
  have hC0 : nodes A 0=0 := by
    unfold nodes
    exact Finset.sum_eq_zero fun j _ => ha 0 j (Nat.zero_le _)
  have hf (j : Fin (s+1)) (hj : qdef A j=0) : onOffEval A z j=f (nodes A j) := by
    rw [onOffEval_on A _ hj]
    exact (extendFeature_mem T z.1 (mem_onNodes.mpr ⟨j,hj,rfl⟩)).symm
  have hz : onOffEval A z 0=0 := origin_zeroSpace A ha 5 hv
  rw [hf 0 hD0,hC0] at hz
  rw [hf i hi]
  let x := nodes A i
  have hxT : x∈T := mem_onNodes.mpr ⟨i,hi,rfl⟩
  change f x=0
  by_cases h0 : x=0
  · rwa [h0]
  have hx : x∈S := Finset.mem_erase.mpr ⟨h0,hxT⟩
  let R := Lagrange.interpolate S id (fun y : K => if y=x then 1 else 0)
  have hR (y) (hy : y∈S) : R.eval y=if y=x then 1 else 0 :=
    Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hy
  have hd : R.natDegree≤3 := by
    by_cases he : R=0
    · simp [he]
    · have hS : S.card+1=T.card := Finset.card_erase_add_one (zero_mem_onNodes ha)
      change T.card=5 at hM
      have hdeg := (Polynomial.natDegree_lt_iff_degree_lt he).mpr
        (Lagrange.degree_interpolate_lt (fun y : K => if y=x then 1 else 0) (Set.injOn_id (↑S : Set K)))
      omega
  have hpair := defect_polynomial_pair_zero ho (by decide : 5+3+1≤9) hv R hd
  rw [row_onOff_eval_eq_onWeights hoff] at hpair
  change (∑ y∈T,onWeight A b y * (R.eval y*f y))=0 at hpair
  rw [Finset.sum_eq_single x] at hpair
  · rw [hR x hx,ite_eq_left rfl,one_mul] at hpair
    exact (mul_eq_zero.mp hpair).resolve_left (order9_five_on_weights_nonzero ho hM hoff hxT)
  · intro y hy hxy
    by_cases hy0 : y=0
    · simp [hy0,hz]
    · rw [hR _ (Finset.mem_erase.mpr ⟨hy0,hy⟩),ite_eq_right hxy,zero_mul,mul_zero]
  · intro h; exact False.elim (h hxT)

end RKCert.Paired

