module

public import RKCert.ReviewedNative.NativeFlatClockHead
public import RKCert.ReviewedNative.ERKHeadContrast
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The joint clock/multiplier contrast at grade eight

A given third-grade multiplier profile forces one genuine nonzero
chronological clock to pay the oriented cubic square primitive. Only
the existing native first-unmatched-block observer is used. -/
namespace RKResearch.Certified.Graded
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
noncomputable section

private theorem joint_labels (c v : Fin (s+1) → K) (U : Submodule K (Fin (s+1)→K))
    (clock : MaskInvariant c U) (value : MaskInvariant v U) :
    ∃ tag : Fin (s+1) → K,
      (∀ i j, tag i=tag j ↔ c i=c j ∧ v i=v j) ∧ MaskInvariant tag U := by
  classical
  let S := (Finset.univ : Finset (Fin (s+1))).image (fun i => (c i,v i))
  let f (i : Fin (s+1)) : S := ⟨(c i,v i),Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let e := Fintype.equivFin S
  let tag (i : Fin (s+1)) : K := ((e (f i)).val : K)
  have tagEq (i j : Fin (s+1)) : tag i=tag j ↔ c i=c j ∧ v i=v j := by
    constructor
    · intro h
      have vals : (e (f i)).val=(e (f j)).val := Nat.cast_injective h
      have eij : f i=f j := e.injective (Fin.ext vals)
      have xy : (c i,v i)=(c j,v j) := congrArg Subtype.val eij
      exact ⟨congrArg Prod.fst xy,congrArg Prod.snd xy⟩
    · rintro ⟨hc,hv⟩
      have hf : f i=f j := Subtype.ext (Prod.ext hc hv)
      simp [tag,hf]
  refine ⟨tag,tagEq,?_⟩
  intro a x hx
  by_cases h : ∃ j, tag j=a
  · obtain ⟨j,rfl⟩ := h
    have he : blockMask tag (tag j) x=blockMask v (v j) (blockMask c (c j) x) := by
      ext i
      by_cases hc : c i=c j <;> by_cases hv : v i=v j <;> simp [blockMask,tagEq,hc,hv]
    rw [he]
    exact value _ _ (clock _ _ hx)
  · have he : blockMask tag a x=0 := by
      ext i
      simp [blockMask,show tag i≠a from fun t => h ⟨i,t⟩]
    rw [he]
    exact U.zero_mem

omit [CharZero K] in
private theorem mismatched_joint_block {c v w label : Fin (s+1) → K} {P : K[X]}
    {U : Submodule K (Fin (s+1)→K)} {n : ℕ}
    (inv : MaskInvariant label U)
    (tagEq : ∀ i j, label i=label j ↔ c i=c j ∧ v i=v j)
    (profile : v*w-weightedEval c w P∈U) {k : Fin (s+1)} (ne : v k≠P.eval (c k))
    {x : Fin (s+1) → K} (hx : x∈chain (diag c) U w n) :
    blockMask label (label k) x∈U := by
  classical
  have fact : blockMask label (label k) (v*w-weightedEval c w P) =
      (v k-P.eval (c k)) • blockMask label (label k) w := by
    ext i
    by_cases hi : label i=label k
    · have tags := (tagEq i k).mp hi
      simp [blockMask,hi,tags.1,tags.2,sub_mul]
    · simp [blockMask,hi]
  have restricted := inv (label k) _ profile
  rw [fact] at restricted
  have hw := (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ne))).mp restricted
  obtain ⟨u,hu,Q,_,eq⟩ := HeadFiber.exists_poly hx
  have e : blockMask label (label k) x =
      blockMask label (label k) u + Q.eval (c k) • blockMask label (label k) w := by
    ext i
    by_cases hi : label i=label k
    · have ec := ((tagEq i k).mp hi).1
      simp [blockMask,hi,eq,ec]
    · simp [blockMask,hi]
  rw [e]
  exact U.add_mem (inv _ _ hu) (U.smul_mem _ hw)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 650000 in
/-- The same actual nonzero clock is measured by the native primitive.
No sign requirement on the clock or coefficient field is used here. -/
theorem grade_eight_cubic_chronology (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder p A b) (pay : 16≤p) {r : ℕ} {U : Submodule K (Fin (s+1)→K)}
    {w v : Fin (s+1)→K} (H : FlatClockHead A 5 3 r U w) (hv : v∈zeroSpace A 3)
    (stable : U.map (diag v) ≤ U)
    (P : K[X]) (pn : P≠0) (pd : P.natDegree≤3)
    (profile : v*w-weightedEval (nodes A) w P∈U) :
    ∃ k : Fin (s+1), nodes A k≠0 ∧ (primitive (X*P^2)).eval (nodes A k)=0 := by
  classical
  let c := nodes A
  let Q : K[X] := X*P
  let z := evalNodes A Q - weightedEval c v X
  have zval (i : Fin (s+1)) : z i = c i*(P.eval (c i)-v i) := by
    simp [z,Q,c,mul_sub]
  have zout : z∉U := by
    intro h
    have eq : weightedEval c v X=diag c v := by ext i; simp
    have v4 : weightedEval c v X∈zeroSpace A 4 := eq.symm ▸ diag_zeroSpace A 3 hv
    have cert := (zeroSpace A 8).add_mem
      (zeroSpace_mono A (by decide : 5≤8) (H.coreInside h))
      (zeroSpace_mono A (by decide : 4≤8) v4)
    have sep : PolySeparated A 8 := PolySeparated.of_coeff (explicit_coeff_separated ha ho pay)
    have dQ : Q.natDegree ≤ 8 := by
      have hd := natDegree_mul_le (p:=X) (q:=P)
      rw [natDegree_X] at hd
      dsimp [Q]
      omega
    exact mul_ne_zero X_ne_zero pn
      (sep Q dQ (by simpa only [z,sub_add_cancel] using cert))
  have clock : MaskInvariant c U :=
    clock_mask_invariant (fun a ha => H.coreStable (Submodule.mem_map_of_mem ha))
  have value : MaskInvariant v U :=
    clock_mask_invariant (fun a ha => stable (Submodule.mem_map_of_mem ha))
  obtain ⟨tag,tagEq,invTag⟩ := joint_labels c v U clock value
  obtain ⟨k,g,hg,prior,bad⟩ := HeadContrast.first_unmatched_block tag z U invTag zout
  have nz : z k≠0 := by
    intro hz
    apply bad
    refine ⟨0,U.zero_mem,fun i _ htag => ?_⟩
    obtain ⟨ec,ev⟩ := (tagEq i k).mp htag
    simpa only [zval,ec,ev,Pi.zero_apply] using hz.symm
  have nk : c k≠0 := by
    intro h
    exact nz (by rw [zval,h,zero_mul])
  have ne : v k≠P.eval (c k) := by
    intro h
    exact nz (by rw [zval,h,sub_self,mul_zero])
  let T : K[X] := X*P^2
  let D : K[X] := P*X
  let feeder := weightedEval c g P + weightedEval c v D
  have dg : weightedEval c g P∈U := by
    have eq : weightedEval c g P = fun i => P.eval (c i)*g i := by ext i; simp
    rw [eq]
    exact mulByBlock_mem c clock (fun x=>P.eval x) hg
  have Ddeg : D.natDegree≤4 := by
    have hh := natDegree_mul_le (p:=P) (q:=(X:K[X]))
    rw [natDegree_X] at hh
    dsimp [D]
    omega
  have stage : weightedEval c v D∈zeroSpace A 7 := by
    have e : weightedEval c v D = v*evalNodes A D := by ext i; simp [c,mul_comm]
    rw [e]
    exact zeroSpace_mul_treeSpace ho (m:=3) (n:=4) (by omega) hv (evalNodes_mem_treeSpace A D Ddeg)
  have feed : feeder∈zeroSpace A 7 :=
    (zeroSpace A 7).add_mem (zeroSpace_mono A (by decide : 5≤7) (H.coreInside dg)) stage
  have td : T.natDegree≤7 := by
    have h := natDegree_mul_le (p:=X) (q:=P^2)
    rw [natDegree_X,natDegree_pow] at h
    dsimp [T]
    omega
  let y := evalNodes A (primitive T) - mat A (evalNodes A T) + mat A feeder
  have y8 : y∈zeroSpace A 8 := (zeroSpace A 8).add_mem
    (by simpa only [neg_sub] using (zeroSpace A 8).neg_mem (primitive_defect A T td))
    (mat_zeroSpace_charZero A 7 feed)
  have pref (i : Fin (s+1)) (hi : i.val<k.val+1) : y i=(primitive T).eval (c i) := by
    have eq : mat A (evalNodes A T) i = mat A feeder i := by
      have h := causal_mat ha i (evalNodes A T-feeder) (by
        intro l hl
        change l.val < i.val at hl
        have hLK : l<k := by change l.val < k.val; omega
        rw [Pi.sub_apply,evalNodes_apply,sub_eq_zero]
        simp only [feeder,Pi.add_apply,weightedEval_apply,prior l hLK,zval]
        simp only [T,D,c,eval_mul,eval_X,pow_two]
        ring)
      simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using h
    change (primitive T).eval (c i) - mat A (evalNodes A T) i + mat A feeder i=_
    rw [eq,sub_add_cancel]
  have ychain := (H.flags 3 (by decide)).le y8
  have masked := mismatched_joint_block invTag tagEq profile ne ychain
  refine ⟨k,nk,?_⟩
  by_contra nonzero
  have nonzero : (primitive T).eval (c k)≠0 := nonzero
  apply bad
  let a := z k/((primitive T).eval (c k))
  refine ⟨a • blockMask tag (tag k) y,(U.smul_mem a masked),?_⟩
  intro i hi e
  obtain ⟨ec,ev⟩ := (tagEq i k).mp e
  simp only [Pi.smul_apply,smul_eq_mul,blockMask,e,ite_true,pref i hi]
  rw [zval i,ec,ev,←zval k]
  exact div_mul_cancel₀ _ nonzero

end
end RKResearch.Certified.Graded
