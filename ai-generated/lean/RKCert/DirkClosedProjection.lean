module

public import RKCert.DirkShortTrace
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-! # Finite-grade chronological reduction without stage deletion

Keep the first representative of each eligible (clock, head) signature,
and keep the original coordinate labels. The discarded coordinates are zeros
in the reduced linear transformations, not silently deleted RK stages.
At each A-application we reinsert the corrected original trace with its
same profile, allowing the commutator to involve two genuine integrations. -/

namespace RKCert.Paired.Reduce
open RKCert.Paired.Clock RKCert.Endpoint RKCert.OneEscape Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable (c w : Vec K s) (U : Submodule K (Vec K s))

def Eligible (i : Fin s) : Prop := ¬ Live U i ∧ (c i ≠ 0 ∨ w i ≠ 0)

def Signature (i : Fin s) : K×K := (c i,w i)

def bucket (i : Fin s) : Finset (Fin s) :=
  Finset.univ.filter fun j => Eligible c w U j ∧ Signature c w j=Signature c w i

theorem bucket_self {i : Fin s} (h : Eligible c w U i) : i∈bucket c w U i :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,rfl⟩

def first (i : Fin s) : Fin s :=
  if h : Eligible c w U i then (bucket c w U i).min' ⟨i,bucket_self c w U h⟩ else i

def Kept (i : Fin s) : Prop := Eligible c w U i ∧ first c w U i=i

variable {c w U}

theorem first_mem_bucket {i : Fin s} (h : Eligible c w U i) :
    first c w U i∈bucket c w U i := by
  rw [first,dite_eq_left h]
  exact Finset.min'_mem _ _

theorem first_le (i : Fin s) : first c w U i ≤ i := by
  unfold first
  split
  · exact Finset.min'_le _ _ (bucket_self c w U (by assumption))
  · rfl

theorem first_eligible {i : Fin s} (h : Eligible c w U i) :
    Eligible c w U (first c w U i) := (Finset.mem_filter.mp (first_mem_bucket h)).2.1

theorem first_signature {i : Fin s} (h : Eligible c w U i) :
    Signature c w (first c w U i)=Signature c w i :=
  (Finset.mem_filter.mp (first_mem_bucket h)).2.2

theorem first_eq_of_signature {i j : Fin s} (hi : Eligible c w U i) (hj : Eligible c w U j)
    (he : Signature c w i=Signature c w j) : first c w U i=first c w U j := by
  have hb : bucket c w U i=bucket c w U j := by
    ext j; simp only [bucket,he]
  simp only [first,dite_eq_left hi,dite_eq_left hj,hb]

theorem first_kept {i : Fin s} (hi : Eligible c w U i) :
    Kept c w U (first c w U i) :=
  ⟨first_eligible hi,first_eq_of_signature (first_eligible hi) hi (first_signature hi)⟩

theorem kept_unique {i j : Fin s} (hi : Kept c w U i) (hj : Kept c w U j)
    (he : Signature c w i=Signature c w j) : i=j :=
  hi.2.symm.trans ((first_eq_of_signature hi.1 hj.1 he).trans hj.2)

variable (c w U)

/-- D is the restriction in original coordinates: all unused slots are zero. -/
def restrict : Vec K s →ₗ[K] Vec K s :=
  LinearMap.pi fun i => if Kept c w U i then LinearMap.proj i else 0

/-- L inserts zero at mask classes and clean zeros and repeats the first same-signature value. -/
def replay : Vec K s →ₗ[K] Vec K s :=
  LinearMap.pi fun i => if Eligible c w U i then LinearMap.proj (first c w U i) else 0

theorem restrict_apply (v : Vec K s) (i : Fin s) :
    restrict c w U v i=if Kept c w U i then v i else 0 := by
  simp only [restrict,LinearMap.pi_apply]
  split <;> rfl

theorem replay_apply (v : Vec K s) (i : Fin s) :
    replay c w U v i=if Eligible c w U i then v (first c w U i) else 0 := by
  simp only [replay,LinearMap.pi_apply]
  split <;> rfl

theorem restrict_clock (v : Vec K s) :
    restrict c w U (diag c v) = diag c (restrict c w U v) := by
  ext i
  by_cases h : Kept c w U i <;> simp [restrict_apply,h]

variable {c w U}
theorem replay_single_of_unkept {j : Fin s} (hj : ¬Kept c w U j) :
    replay c w U (Pi.single j (1:K))=0 := by
  ext i
  rw [replay_apply]
  by_cases hi : Eligible c w U i
  · have hn : j≠first c w U i := fun h => hj (h ▸ first_kept hi)
    simp [hi,hn.symm]
  · simp [hi]

variable {A : Fin s → Fin s → K}

def foldMatrix (A : Fin s → Fin s → K) (w : Vec K s) (U : Submodule K (Vec K s)) :
    Matrix (Fin s) (Fin s) K :=
  LinearMap.toMatrix'
    ((restrict (nodes A) w U).comp ((mat A).comp (replay (nodes A) w U)))

theorem foldMatrix_mul (A : Fin s → Fin s → K) (w : Vec K s)
    (U : Submodule K (Vec K s)) (v : Vec K s) :
    mat (foldMatrix A w U) v = restrict (nodes A) w U (mat A (replay (nodes A) w U v)) := by
  change Matrix.toLin' (LinearMap.toMatrix' _) v = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem foldMatrix_zero_row {i j : Fin s} (hi : ¬Kept (nodes A) w U i) :
    foldMatrix A w U i j=0 := by
  simp [foldMatrix,restrict_apply,hi]

theorem foldMatrix_zero_col {i j : Fin s} (hj : ¬Kept (nodes A) w U j) :
    foldMatrix A w U i j=0 := by
  simp [foldMatrix,replay_single_of_unkept hj]

/-- Folding a later duplicate into its first representative never creates
a tap from a later position. Arbitrary original lower triangles are allowed. -/
theorem foldMatrix_lower (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (i j : Fin s) (hij : i.val<j.val) : foldMatrix A w U i j=0 := by
  have h : mat A (replay (nodes A) w U (Pi.single j (1:K))) i=0 := by
    rw [mat_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i<k
    · rw [ha i k hk,zero_mul]
    · have e : ¬j=first (nodes A) w U k := by
        intro eq
        have hh := (first_le (c:=nodes A) (w:=w) (U:=U) k).trans (le_of_not_gt hk)
        rw [←eq] at hh
        exact (not_le.mpr hij) hh
      rw [replay_apply]
      split
      · rw [Pi.single_eq_of_ne (Ne.symm e),mul_zero]
      · simp
  simp [foldMatrix,restrict_apply,h]


/-- After zeroing a mask class, repeating a signature and deleting a clean
origin, the reinserted vector is still an actual same-profile trace. -/
theorem replay_trace {P : K[X]} {v : Vec K s} {n ℓ : ℕ}
    (hU : U.map (diag (nodes A))≤U) (hUF : U≤zeroSpace A n)
    (hAlgebra : MulClosed U) (hLive : ∀ i, Live U i → w i=0)
    (hBand : zeroSpace A n ≤ chain (diag (nodes A)) U w ℓ)
    (h : OrdinaryTrace A n v P) (hP0 : P.eval 0=0) :
    OrdinaryTrace A n (replay (nodes A) w U (restrict (nodes A) w U v)) P := by
  obtain ⟨e,he,heval⟩ := core_indicator hAlgebra
  obtain ⟨u,hu,Q,_,hQ⟩ := exists_head_poly (hBand h.pure)
  have hv (i : Fin s) : v i=P.eval (nodes A i)+u i+Q.eval (nodes A i)*w i := by
    have hi := hQ i
    simp only [Pi.sub_apply,evalNodes_apply] at hi
    rw [sub_eq_iff_eq_add] at hi
    rw [hi]
    ring
  have uz (i : Fin s) (hn : ¬Live U i) : u i=0 := by
    by_contra h'
    exact hn ⟨u,hu,h'⟩
  let ep : Vec K s := fun i => P.eval (nodes A i)*e i
  have epmem : ep∈U := poly_preserves hU P e he
  have eq : replay (nodes A) w U (restrict (nodes A) w U v)=v-(ep+u) := by
    ext i
    rw [replay_apply]
    change _=v i-(ep i+u i)
    by_cases hi : Eligible (nodes A) w U i
    · let j := first (nodes A) w U i
      have hj := first_eligible hi
      have b := first_signature hi
      have e₁ : nodes A j=nodes A i := congrArg Prod.fst b
      have e₂ : w j=w i := congrArg Prod.snd b
      have same : v j=v i := by rw [hv,hv,e₁,e₂,uz _ hi.1,uz _ hj.1]
      rw [ite_eq_left hi,restrict_apply,ite_eq_left (first_kept hi),same]
      simp [ep,heval,hi.1,uz _ hi.1]
    · rw [ite_eq_right hi]
      by_cases hT : Live U i
      · simp [hv,ep,heval,hT,hLive i hT]
      · have hc : nodes A i=0 := by by_contra ht; exact hi ⟨hT,Or.inl ht⟩
        have hw : w i=0 := by by_contra ht; exact hi ⟨hT,Or.inr ht⟩
        simp [hv,ep,heval,hT,uz _ hT,hc,hw,hP0]
  rw [eq]
  exact h.sub_pure (hUF (U.add_mem epmem hu))

variable {P : K[X]} {v : Vec K s}

/-- Genuine application of the reduced matrix: Bv is D applied to an
original A-image of the SAME profile, with one added grade. -/
theorem fold_primitive [CharZero K] (h : Grade3Head A U w P) {n : ℕ} (hl : 3≤n) (hu : n≤6)
    {f : K[X]} (ht : OrdinaryTrace A n v f) (hf0 : f.eval 0=0) :
    ∃ z : Vec K s, OrdinaryTrace A (n+1) z (formalPrimitive f) ∧
      mat (foldMatrix A w U) (restrict (nodes A) w U v)=restrict (nodes A) w U z := by
  have e := h.band (n-3) (by omega)
  rw [show 3+(n-3)=n by omega] at e
  have hR := replay_trace h.invariant (h.core.trans (zeroSpace_mono A hl))
    h.mulClosed h.disjoint e.le ht hf0
  exact ⟨_,hR.primitive,foldMatrix_mul A w U _⟩

/-- The reduced commutator does not represent the original commutator on
arbitrary columns. This formula is only for paid traces with f(0)=0 and
replays the correction between EACH of the two applications of A. -/
theorem fold_commutator [CharZero K] (h : Grade3Head A U w P) {n : ℕ} (hl : 3≤n) (hu : n≤4)
    {f : K[X]} (ht : OrdinaryTrace A n v f) (hf0 : f.eval 0=0) :
    ∃ z∈zeroSpace A (n+2), commutatorR (mat (foldMatrix A w U)) (diag (nodes A))
      (restrict (nodes A) w U v)=restrict (nodes A) w U z := by
  let D := restrict (nodes A) w U
  let Xmap := diag (nodes A)
  let M := mat (foldMatrix A w U)
  obtain ⟨v₁,hv₁,eq₁⟩ := fold_primitive h hl (by omega) ht hf0
  obtain ⟨v₂,hv₂,eq₂⟩ := fold_primitive h (n:=n+1) (by omega) (by omega) ht.clock (by simp)
  obtain ⟨v₃,hv₃,eq₃⟩ := fold_primitive h (n:=n+1) (by omega) (by omega) hv₁ (by simp)
  refine ⟨Xmap v₁-v₂-v₃,?_,?_⟩
  · have htrace := (hv₁.clock.sub hv₂).sub hv₃
    rw [primitive_commutation] at htrace
    exact htrace.pure_zero
  · change Xmap (M (D v)) - M (Xmap (D v)) - M (M (D v)) = D (Xmap v₁-v₂-v₃)
    change M (D v)=D v₁ at eq₁
    change M (D (Xmap v))=D v₂ at eq₂
    change M (D v₁)=D v₃ at eq₃
    have hD : D (Xmap v)=Xmap (D v) := restrict_clock _ _ _ _
    have hD₁ : D (Xmap v₁)=Xmap (D v₁) := restrict_clock _ _ _ _
    rw [map_sub,map_sub,eq₁,eq₃,hD₁,←hD,eq₂]

theorem fold_defect_pattern (h : Grade3Head A U w P) {k : ℕ} (hk : k≤3)
    {v : Vec K s} (hv : v∈zeroSpace A (3+k)) :
    ∃ Q : K[X], Q.natDegree≤k ∧ ∀ i : Fin s,
      restrict (nodes A) w U v i =
        if Kept (nodes A) w U i then Q.eval (nodes A i)*w i else 0 := by
  rw [h.band k hk] at hv
  obtain ⟨u,hu,Q,hdeg,heq⟩ := exists_head_poly hv
  have hq : Q.natDegree≤k := by
    by_cases hQ : Q=0
    · simp [hQ]
    have hh := (natDegree_lt_iff_degree_lt hQ).mpr hdeg
    omega
  refine ⟨Q,hq,fun i => ?_⟩
  rw [restrict_apply]
  by_cases hi : Kept (nodes A) w U i
  · have hz : u i=0 := by by_contra hn; exact hi.1.1 ⟨u,hu,hn⟩
    simp [hi,heq i,hz]
  · simp [hi]

end
end RKCert.Paired.Reduce
