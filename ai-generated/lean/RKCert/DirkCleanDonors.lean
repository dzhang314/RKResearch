module

public import RKCert.DirkCutLinear

@[expose] public section

namespace RKCert.Paired.Reduce
open RKCert.Paired.Clock RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s} {P : K[X]}

def beforeDirty (A : Fin s → Fin s → K) (w : Vec K s) (U : Submodule K (Vec K s))
    (i : Fin s) : Finset (Fin s) := Finset.univ.filter (fun j => j < i ∧ Dirty (nodes A) w U j)

omit [CharZero K] in
theorem mem_beforeDirty {i j : Fin s} :
    j∈beforeDirty A w U i ↔ j < i ∧ Dirty (nodes A) w U j := by simp [beforeDirty]

theorem exists_first_of {R : Fin s → Prop} (h : ∃ i,R i) :
    ∃ i, R i ∧ ∀ j < i, ¬R j := by
  let S := Finset.univ.filter R
  obtain ⟨j,hj⟩ := h
  have hS : S.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let i := S.min' hS
  refine ⟨i,(Finset.mem_filter.mp (S.min'_mem hS)).2,fun j hj hr => ?_⟩
  exact (not_le.mpr hj) (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩))

theorem clean_tap_moment (h : Grade3Head A U w P) (ha : LowerArray A)
    {i : Fin s} (hi : Clean (nodes A) w U i)
    (hpre : ∀ j < i, ¬Clean (nodes A) w U j) (Q : K[X]) (hQ : Q.natDegree≤2) :
    ∑ j∈beforeDirty A w U i, (foldMatrix A w U i j*w j)*Q.eval (nodes A j)=0 := by
  let t : Vec K s := fun j => Q.eval (nodes A j)*w j
  have htr : OrdinaryTrace A 5 t 0 := by
    refine ⟨by simp,?_⟩
    have e : evalNodes A (0:K[X])=0 := by ext j; simp
    rw [e,sub_zero]
    exact head_polynomial_mem h (k:=2) (by decide) Q hQ
  have huv := fold_clean_value h (n:=5) (by decide) (by decide) htr (by simp) hi
  have ho : (formalPrimitive (0:K[X])).eval (nodes A i)=0 := by
    change (formalPrimitiveLinear (0:K[X])).eval (nodes A i)=0
    simp
  rw [ho,row_restrict_sum _ _ _ (beforeDirty A w U i) ?_] at huv
  · rw [←huv]
    apply Finset.sum_congr rfl
    intro j hj
    rw [restrict_apply,ite_eq_left (mem_beforeDirty.mp hj).2.1]
    dsimp [t]
    ring
  · intro j hj
    rcases lt_trichotomy j i with hlt|rfl|hlt
    · by_cases hkept : Kept (nodes A) w U j
      · rcases clean_or_dirty hkept with hcl|hdi
        · exact False.elim (hpre j hlt hcl)
        · exact False.elim (hj (mem_beforeDirty.mpr ⟨hlt,hdi⟩))
      · exact Or.inl (foldMatrix_zero_col hkept)
    · exact Or.inr (by simp [restrict_apply,t,hi.2])
    · exact Or.inl (foldMatrix_lower ha _ _ hlt)

/-- At its earliest clean row at least one earlier dirty tap is nonzero;
otherwise scalar x and x² would require two different diagonal values. -/
theorem some_clean_tap (h : Grade3Head A U w P) (ha : LowerArray A)
    {i : Fin s} (hi : Clean (nodes A) w U i)
    (hpre : ∀ j < i, ¬Clean (nodes A) w U j) :
    ∃ j∈beforeDirty A w U i, foldMatrix A w U i j≠0 := by
  by_contra hh
  let B := foldMatrix A w U
  let c := nodes A
  have all (j : Fin s) (hne : j≠i) : B i j=0 := by
    rcases lt_or_gt_of_ne hne with hl|hl
    · by_cases hkept : Kept c w U j
      · rcases clean_or_dirty hkept with hcl|hdi
        · exact False.elim (hpre j hl hcl)
        · by_contra hnot
          exact hh ⟨j,mem_beforeDirty.mpr ⟨hl,hdi⟩,hnot⟩
      · exact foldMatrix_zero_col hkept
    · exact foldMatrix_lower ha _ _ hl
  have eq (f : K[X]) (hdeg : f.natDegree≤3) (hf0 : f.eval 0=0) :
      B i i*f.eval (c i)=(formalPrimitive f).eval (c i) := by
    have ex := fold_clean_value h (n:=3) (by decide) (by decide)
      (OrdinaryTrace.scalar A hdeg) hf0 hi
    rw [row_single_tap B i i _ (fun j hj => Or.inl (all j hj)),
      restrict_apply,ite_eq_left hi.1,evalNodes_apply] at ex
    exact ex
  have h1 := eq X (by simp) (by simp)
  have h2 := eq (X^2) (by simp) (by simp)
  rw [eval_X,primitive_X_eval] at h1
  rw [eval_pow,eval_X,primitive_X_sq_eval] at h2
  have c0 : c i≠0 := clean_clock hi
  have d1 : B i i=c i/2 := by
    apply mul_right_cancel₀ c0
    rw [h1]
    ring
  have d2 : B i i=c i/3 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 c0)
    rw [h2]
    ring
  apply c0
  linear_combination 6*(d2-d1)

theorem at_least_four_clean_donors (h : Grade3Head A U w P) (ha : LowerArray A)
    {i : Fin s} (hi : Clean (nodes A) w U i)
    (hpre : ∀ j < i, ¬Clean (nodes A) w U j) :
    4≤(beforeDirty A w U i).card := by
  by_contra! hc
  obtain ⟨j,hj,hn⟩ := some_clean_tap h ha hi hpre
  have hIn : Set.InjOn (nodes A) (beforeDirty A w U i : Finset (Fin s)) :=
    fun x hx y hy he => dirty_distinct h (mem_beforeDirty.mp hx).2 (mem_beforeDirty.mp hy).2 he
  have zero := vanish_taps (beforeDirty A w U i) (nodes A)
    (fun j => foldMatrix A w U i j*w j) (d:=2) hIn (by omega)
    (clean_tap_moment h ha hi hpre) j hj
  exact hn ((mul_eq_zero.mp zero).resolve_right (mem_beforeDirty.mp hj).2.2)

/-- Any fourth tap at the first clean receiver is genuinely nonzero if exactly
four dirty predecessors are present. The output weights are not involved. -/
theorem all_four_clean_taps (h : Grade3Head A U w P) (ha : LowerArray A)
    {i : Fin s} (hi : Clean (nodes A) w U i)
    (hpre : ∀ j < i, ¬Clean (nodes A) w U j)
    (hcard : (beforeDirty A w U i).card=4) :
    ∀ j∈beforeDirty A w U i, foldMatrix A w U i j≠0 := by
  intro j hj he
  let T := beforeDirty A w U i
  let t := T.erase j
  have ht : t.card=3 := by
    have h := Finset.card_erase_add_one hj
    change t.card+1=T.card at h
    change T.card=4 at hcard
    omega
  have hIn : Set.InjOn (nodes A) t :=
    fun x hx y hy hxy => dirty_distinct h
      (mem_beforeDirty.mp (Finset.mem_of_mem_erase hx)).2
      (mem_beforeDirty.mp (Finset.mem_of_mem_erase hy)).2 hxy
  have hzero (Q : K[X]) (hQ : Q.natDegree≤2) :
      ∑ k∈t, (foldMatrix A w U i k*w k)*Q.eval (nodes A k)=0 := by
    have hh := clean_tap_moment h ha hi hpre Q hQ
    rw [←Finset.insert_erase hj,Finset.sum_insert (Finset.notMem_erase _ _)] at hh
    simpa [t,he] using hh
  have hz := vanish_taps t (nodes A) (fun k => foldMatrix A w U i k*w k) (d:=2)
    hIn (by omega) hzero
  obtain ⟨l,hl,hn⟩ := some_clean_tap h ha hi hpre
  by_cases ea : l=j
  · exact hn (ea.symm ▸ he)
  · exact hn ((mul_eq_zero.mp (hz l (Finset.mem_erase.mpr ⟨ea,hl⟩))).resolve_right
      (mem_beforeDirty.mp hl).2.2)

/-- The first retained clean row is already a nonroot of the head polynomial.
This result genuinely uses both paid clean primitives and the first pivot's
actual reduced diagonal; it does not presume a uniformly explicit tableau. -/
theorem first_clean_nonroot (h : Grade3Head A U w P) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    {u : Fin s} (hu : Clean (nodes A) w U u)
    (hpre : ∀ j < u, ¬Clean (nodes A) w U j) :
    P.eval (nodes A u)≠0 ∧ foldMatrix A w U u u=0 := by
  obtain ⟨v,⟨hv,hPv⟩,hvec⟩ := exists_first_of (exists_clean_nonroot h ho hp)
  obtain ⟨θ,hθ,hval⟩ := clean_contrast h
  let c := nodes A
  let B := foldMatrix A w U
  let D := restrict c w U
  let x := diag c θ
  let z := diag c x
  have hx : OrdinaryTrace A 4 x (X*P) := hθ.clock
  have hz : OrdinaryTrace A 5 z (X*(X*P)) := hx.clock
  have hθz (i : Fin s) (hi : i < v) : D x i=0 := by
    by_cases hk : Kept c w U i
    · rcases clean_or_dirty hk with hcl|hdi
      · have hp0 : P.eval (nodes A i)=0 := by
          by_contra ht; exact hvec i hi ⟨hcl,ht⟩
        simp [D,x,restrict_apply,hcl.1,hval i,hcl.1.1.1,hcl.2,hp0]
      · simp [D,x,restrict_apply,hdi.1,hval i,hdi.2]
    · simp [D,restrict_apply,hk]
  have vX : D x v≠0 := by
    rw [show D x v=restrict c w U x v from rfl,restrict_apply,ite_eq_left hv.1]
    change c v*θ v≠0
    rw [hval v]
    simp only [hv.1.1.1,hv.2,ne_eq,not_true_eq_false,or_self,ite_false]
    exact mul_ne_zero (clean_clock hv) hPv
  have vdiag : B v v=0 := by
    obtain ⟨Q,_,hQ⟩ := reduced_commutator_pattern h (k:=1) (by decide) hx (by simp)
    have hR := hQ v
    change commutatorR (mat B) (diag c) (D x) v = _ at hR
    rw [commutatorR_leading (foldMatrix_lower ha) hθz,ite_eq_left hv.1,hv.2,mul_zero] at hR
    exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp hR).resolve_right vX))
  have evalX (i : Fin s) (hi : Clean c w U i) :
      mat B (D x) i=(formalPrimitive (X*P)).eval (c i) :=
    fold_clean_value h (by decide) (by decide) hx (by simp) hi
  have evalZ (i : Fin s) (hi : Clean c w U i) :
      mat B (D z) i=(formalPrimitive (X*(X*P))).eval (c i) :=
    fold_clean_value h (by decide) (by decide) hz (by simp) hi
  have dz : D z=diag c (D x) := restrict_clock _ _ _ _
  have vx : (formalPrimitive (X*P)).eval (c v)=0 := by
    rw [←evalX v hv]
    simpa only [vdiag,zero_mul] using causalDiag_mat (A:=B) (foldMatrix_lower ha) v (D x) hθz
  have vz : (formalPrimitive (X*(X*P))).eval (c v)=0 := by
    rw [←evalZ v hv]
    simpa only [vdiag,zero_mul] using causalDiag_mat (A:=B) (foldMatrix_lower ha) v (D z)
      (fun j hj => by simp [dz,hθz j hj])
  have uv : u ≤ v := by
    by_contra! ht; exact hpre v ht hv
  have he : u=v := by
    by_contra hne
    have hl := lt_of_le_of_ne uv hne
    have ux : (formalPrimitive (X*P)).eval (c u)=0 := by
      rw [←evalX u hu]
      exact mat_zero_before (foldMatrix_lower ha) hθz u hl
    have uz : (formalPrimitive (X*(X*P))).eval (c u)=0 := by
      rw [←evalZ u hu]
      exact mat_zero_before (foldMatrix_lower ha) (fun j hj => by simp [dz,hθz j hj]) u hl
    exact two_clean_primitive_impossible P (fun hz=>h.constant_ne (by simp [hz])) h.degree
      (c u) (c v) (clean_clock hu) (clean_clock hv) (fun e=>hne (clean_distinct hu hv e))
      ux uz vx vz
  subst u
  exact ⟨hPv,vdiag⟩

end
end RKCert.Paired.Reduce
