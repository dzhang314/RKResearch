module
public import RKCert.ReviewedNative.OrderNineCohortAdjoint

@[expose] public section

/-! # Tag-aware quadrature and state-valued moments on original rows -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s p : ℕ}

/-- Generic all-physical row tests. Each clock is tagged before
aggregation, so a shared clock never merges clean and defective rows. -/
theorem defect_polynomial_pair_zero {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder A b p) {j q : ℕ} (pay : j+q+1≤p)
    {v : Fin s→K} (hv : v∈zeroSpace A j) (P : K[X]) (hp : P.natDegree≤q) :
    row b (diag (evalNodes A P) v)=0 := by
  rw [evalNodes_eq_coeffEval A P hp,coeffEval_apply]
  have eq : diag (∑ i : Fin (q+1),P.coeff i.val • normTree A (clockTree i.val)) v =
      diag v (∑ i : Fin (q+1),P.coeff i.val • normTree A (clockTree i.val)) := by
    ext i; simp [mul_comm]
  rw [eq,map_sum,map_sum]
  exact Finset.sum_eq_zero (fun i _=>by
    rw [map_smul,map_smul,normTree_clockTree]
    have e : row b (diag v (fun j=>nodes A j ^ i.val))=probe A b i.val v := by
      simp only [row_apply,dotProduct,diag_apply]
      exact Finset.sum_congr rfl (fun _ _=>by ring)
    rw [e,probe_zeroSpace ho (by have :=i.isLt; omega) hv,smul_zero])

noncomputable def onWeight (A : Matrix (Fin s) (Fin s) K) (b : (Fin s→K)) (x : K) : K :=
  ∑ i, if OneOff.g A i=0 ∧ nodes A i=x then b i else 0

/-- Exact scalar quadrature on the on-node fibers, after cancellation
of the off output weights; no sign or simplicity assumption is needed. -/
theorem probe_eq_on_weights {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (hoff : ∀ x∈offKnots A, offMass A b x=0)
    (P : K[X]) (k : ℕ) :
    probe A b k (evalNodes A P) = ∑ x∈cleanKnots A, onWeight A b x * (x^k*P.eval x) := by
  let f (x : K) := x^k*P.eval x
  have he (i : Fin s) : b i*nodes A i^k*P.eval (nodes A i) =
      (if OneOff.g A i=0 then b i*f (nodes A i) else 0) +
      (if OneOff.g A i≠0 then b i*f (nodes A i) else 0) := by
    by_cases h : OneOff.g A i=0 <;> simp [h,f,mul_assoc]
  simp only [probe,row_apply,dotProduct,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib,
    RKCert.Paired.sum_tagged_fibers b (nodes A) (fun i => OneOff.g A i=0) f,
    RKCert.Paired.sum_tagged_fibers b (nodes A) (fun i => OneOff.g A i≠0) f]
  change _ + (∑ x∈offKnots A, offMass A b x * f x) = _
  have hOff : (∑ x∈offKnots A, offMass A b x * f x)=0 :=
    Finset.sum_eq_zero (fun x hx => by rw [hoff x hx,zero_mul])
  rw [hOff,add_zero]
  rfl

/-- Polynomial moment injectivity without the origin hypothesis. -/
theorem zero_of_full_profile_probes {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder A b p) (q : ℕ) (hp : 2*q+1 ≤ p)
    (P : K[X]) (hd : P.natDegree ≤ q)
    (hm : ∀ i : Fin (q+1), probe A b i.val (evalNodes A P)=0) : P=0 := by
  let a : Fin (q+1) → K := fun j => P.coeff j.val
  have hs (i : Fin (q+1)) : (∑ j : Fin (q+1), a j / ((i.val+j.val+1:ℕ):K))=0 := by
    have h := hm i
    rwa [evalNodes_eq_coeffEval A P hd,probe_coeffEval ho (by omega)] at h
  have hz := moments_detect ho (d:=1) (by decide) (by omega) (fun i j => by omega) a hs
  ext n
  by_cases h : n < q+1
  · exact hz ⟨n,h⟩
  · simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n))

theorem order9_five_on_weights_nonzero {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder A b 9) (hM : (cleanKnots A).card=5)
    (hoff : ∀ x∈offKnots A, offMass A b x=0)
    {x : K} (hx : x∈cleanKnots A) : onWeight A b x≠0 := by
  intro hz
  let S := (cleanKnots A).erase x
  let Q := nodalHull S
  have hc : S.card+1=(cleanKnots A).card := Finset.card_erase_add_one hx
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

theorem row_onOff_eval_eq_onWeights {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (hoff : ∀ x∈offKnots A, offMass A b x=0)
    (z : (cleanKnots A → K) × (offKnots A → K)) (P : K[X]) :
    row b (diag (evalNodes A P) (onOffEval A z)) =
      ∑ x∈cleanKnots A, onWeight A b x * (P.eval x*extendFeature (cleanKnots A) z.1 x) := by
  let S := offKnots A
  let T := cleanKnots A
  let f (x : K) := P.eval x * extendFeature T z.1 x
  let g (x : K) := P.eval x * extendFeature S z.2 x
  have he (i : Fin s) : b i*(P.eval (nodes A i)*onOffEval A z i) =
      (if OneOff.g A i=0 then b i*f (nodes A i) else 0) +
      (if OneOff.g A i≠0 then b i*g (nodes A i) else 0) := by
    by_cases h : OneOff.g A i=0
    · rw [onOffEval_on A _ h]
      simp [h,f,extendFeature_mem T z.1 (mem_cleanKnots.mpr ⟨i,h,rfl⟩)]
    · rw [onOffEval_off A _ h]
      simp [h,g,extendFeature_mem S z.2 (mem_offKnots.mpr ⟨i,h,rfl⟩)]
  simp only [row_apply,dotProduct,diag_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib,
    RKCert.Paired.sum_tagged_fibers b (nodes A) (fun i => OneOff.g A i=0) f,
    RKCert.Paired.sum_tagged_fibers b (nodes A) (fun i => OneOff.g A i≠0) g]
  change _ + (∑ x∈S, offMass A b x * g x) = _
  have hOff : (∑ x∈S, offMass A b x * g x)=0 :=
    Finset.sum_eq_zero (fun x hx => by rw [hoff x hx,zero_mul])
  rw [hOff,add_zero]
  rfl

/-- Only after actual E5 is state-valued can the four nonzero on-node
moment equations turn every fifth-grade defect into an on-row zero. -/
theorem state_defect_five_zero_on [CharZero K] {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {b : (Fin (s+1)→K)} (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (hM : (cleanKnots A).card=5)
    (hoff : ∀ x∈offKnots A, offMass A b x=0)
    {v : (Fin (s+1)→K)} (hv : v∈zeroSpace A 5) (hstate : v∈onOffSpace A)
    {i : Fin (s+1)} (hi : OneOff.g A i=0) : v i=0 := by
  obtain ⟨z,rfl⟩ := hstate
  let T := cleanKnots A
  let S := T.erase 0
  let f := extendFeature T z.1
  have hD0 : OneOff.g A (0 : Fin (s+1))=0 := origin_zeroSpace ha 2 (mDef_mem A 1)
  have hC0 : nodes A 0=0 := by
    change (∑ j, A 0 j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have hf (j : Fin (s+1)) (hj : OneOff.g A j=0) : onOffEval A z j=f (nodes A j) := by
    rw [onOffEval_on A _ hj]
    exact (extendFeature_mem T z.1 (mem_cleanKnots.mpr ⟨j,hj,rfl⟩)).symm
  have hz : onOffEval A z 0=0 := origin_zeroSpace ha 5 hv
  rw [hf 0 hD0,hC0] at hz
  rw [hf i hi]
  let x := nodes A i
  have hxT : x∈T := mem_cleanKnots.mpr ⟨i,hi,rfl⟩
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
    · have hS : S.card+1=T.card := Finset.card_erase_add_one (zero_mem_cleanKnots ha)
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


theorem treeSpace_four_profile {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder A b 9) {v : Fin s→K} (hv : v∈treeSpace A 4) (hF : zeroSpace A 4=band A 2) :
    ∃ Q R : K[X], Q.natDegree≤4 ∧ R.natDegree≤2 ∧
      evalNodes A Q+diag (OneOff.g A) (evalNodes A R)=v := by
  rw [treeSpace_coeff_sup ho (by decide),Submodule.mem_sup] at hv
  obtain ⟨u,⟨a,rfl⟩,w,hw,rfl⟩ := hv
  obtain ⟨Q,dq,eq⟩ := band_iff.mp (hF ▸ hw)
  refine ⟨ofFn 5 a,Q,Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _),dq,?_⟩
  rw [ofFn_eval A 4,←eq]

theorem gradeFive_profiles_state_valued {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (fit : ∀i,OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i) : gradeFiveStateSpace A≤onOffSpace A := by
  rintro _ ⟨z,rfl⟩
  rw [gradeFiveStateMap_eq_eval]
  exact pairProfile_mem_onOffSpace fit _ _

theorem sup_singleton_eq_of_rank {V W : Submodule K (Fin s→K)} {w : Fin s→K}
    (inc : V≤W) (mem : w∈W) (out : w∉V) (cap : finrank K W≤finrank K V+1) :
    W=V⊔Submodule.span K {w} := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
    (sup_le inc ((Submodule.span_singleton_le_iff_mem ..).mpr mem))
  rwa [Submodule.finrank_sup_span_singleton out]
end RKResearch.Certified.Graded.MultiOff
