module
public import RKCert.ReviewedNative.OrderNineCohortSupport

@[expose] public section

/-! # Exact physical row gathering; the transpose retains the adjacent row-difference debit -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s n : ℕ}

noncomputable def gatherRow (rep : Fin s → Fin n) : (Fin s→K) →ₗ[K] (Fin n→K) where
  toFun b i := ∑ j, if rep j=i then b j else 0
  map_add' b c := by
    ext i
    simp only [Pi.add_apply,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : rep j=i <;> simp [h]
  map_smul' a b := by
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : rep j=i <;> simp [h]

theorem gatherRow_apply (rep : Fin s → Fin n) (w : (Fin s→K)) (i : Fin n) :
    gatherRow rep w i=∑ j, if rep j=i then w j else 0 := rfl

theorem gatherRow_pair (rep : Fin s → Fin n) (w : (Fin s→K)) (v : (Fin n→K)) :
    row (gatherRow rep w) v=row w (v∘rep) := by
  simp only [row_apply,dotProduct,gatherRow_apply,Function.comp_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (rep j)]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

def lowPrefix10 (i : Fin 10) : Fin 12 := Fin.castLE (by decide) i

def prefixMat10 (A : Matrix (Fin 12) (Fin 12) K) : Matrix (Fin 10) (Fin 10) K :=
  prefixMatrix A (by decide)

theorem prefixMat10_strict {A : Matrix (Fin 12) (Fin 12) K} (ha : ∀i j,i≤j → A i j=0) :
    ∀ i j,i≤j → prefixMat10 A i j=0 := prefix_strict_lower ha (by decide)

theorem sum_ten_two {M : Type*} [AddCommMonoid M] (f : Fin 12 → M) :
    (∑ i,f i)=(∑ i : Fin 10,f (lowPrefix10 i))+f (10:Fin 12)+f (11:Fin 12) := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  rfl

theorem gather_prefix_only (rep : Fin 12 → Fin 10)
    (hRep : ∀ i, rep (lowPrefix10 i)=i)
    (w : (Fin 12→K)) (h10 : w (10:Fin 12)=0) (h11 : w (11:Fin 12)=0) :
    ∀ i, gatherRow rep w i=w (lowPrefix10 i) := by
  intro i
  rw [gatherRow_apply,sum_ten_two]
  simp only [hRep,h10,h11,ite_self,add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h; simp [h]
  · simp

theorem stage_node_eq_of_state {A : Matrix (Fin s) (Fin s) K} {i j : Fin s}
    (h : lowStateAt A i=lowStateAt A j) : nodes A i=nodes A j := by
  let v : (Fin s→K) := onOffEval A (fun x=>x.val,fun x=>x.val)
  have hv : v∈onOffSpace A := ⟨_,rfl⟩
  have hV (l : Fin s) : v l=nodes A l := by
    dsimp [v]
    by_cases hg : g A l=0
    · rw [onOffEval_on A _ hg]
    · rw [onOffEval_off A _ hg]
  simpa only [hV] using onOffSpace_eq_at_states h hv

/-- If the last physical receiver's weight is zero, pushing forward
the actual transpose differs from the prefix transpose by the exact
row difference at the sole intermediate receiver. -/
theorem gather_transMat_ten {A : Matrix (Fin 12) (Fin 12) K} (ha : ∀i j,i≤j → A i j=0)
    (rep : Fin 12 → Fin 10) (hRep : ∀ i, rep (lowPrefix10 i)=i)
    (w : (Fin 12→K)) (hEnd : w (11:Fin 12)=0) :
    gatherRow rep (transMat A w) =
      transMat (prefixMat10 A) (gatherRow rep w) +
        w (10:Fin 12) • fun i => A 10 (lowPrefix10 i)-A (lowPrefix10 (rep 10)) (lowPrefix10 i) := by
  ext i
  let e : (Fin 10→K) := Pi.single i 1
  have he (j : Fin 12) (hj : j ≤ (10:Fin 12)) :
      mat A (e∘rep) j=A j (lowPrefix10 i) := by
    rw [mat_apply,Matrix.mulVec,dotProduct,sum_ten_two]
    have h10 : A j (10:Fin 12)=0 := ha _ _ hj
    have h11 : A j (11:Fin 12)=0 := ha _ _ (hj.trans (by decide))
    simp only [Function.comp_apply,hRep,h10,h11,zero_mul,add_zero]
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro k _ hk; simp [e,hk]
    · simp
  have hL :
      gatherRow rep (transMat A w) i =
        (∑ j : Fin 10, w (lowPrefix10 j)*A (lowPrefix10 j) (lowPrefix10 i))+
          w (10:Fin 12)*A 10 (lowPrefix10 i) := by
    rw [← row_single_eq_coord (gatherRow rep (transMat A w)) i]
    change row (gatherRow rep (transMat A w)) e=_
    rw [gatherRow_pair,row_flip_mat,row_apply,dotProduct,sum_ten_two,hEnd,zero_mul,add_zero]
    rw [he 10 le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [he _ (by exact j.isLt.le)]
  have hB :
      transMat (prefixMat10 A) (gatherRow rep w) i =
        (∑ j : Fin 10, w (lowPrefix10 j)*A (lowPrefix10 j) (lowPrefix10 i))+
          w (10:Fin 12)*A (lowPrefix10 (rep 10)) (lowPrefix10 i) := by
    have hEq : transMat (prefixMat10 A) (gatherRow rep w) i =
        row (gatherRow rep w) (fun j => A (lowPrefix10 j) (lowPrefix10 i)) := by
      simp only [transMat,mat_apply,Matrix.mulVec,Matrix.transpose_apply,row_apply,dotProduct,
        prefixMat10,prefixMatrix,Matrix.submatrix_apply,lowPrefix10,mul_comm]
    rw [hEq,gatherRow_pair,row_apply,dotProduct,sum_ten_two,hEnd,zero_mul,add_zero]
    simp only [Function.comp_apply,hRep]
  rw [hL,Pi.add_apply,hB,Pi.smul_apply,smul_eq_mul]
  ring

theorem gather_multiply_by_nodes {A : Matrix (Fin 12) (Fin 12) K}
    (rep : Fin 12 → Fin 10) (hNode : ∀ i, nodes A i=nodes A (lowPrefix10 (rep i)))
    (b : (Fin 12→K)) (f : K→K) :
    gatherRow rep (fun i => b i*f (nodes A i)) =
      fun i => gatherRow rep b i*f (nodes A (lowPrefix10 i)) := by
  ext i
  simp only [gatherRow_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : rep j=i
  · simp [h,hNode j]
  · simp [h]

def lateResidual {n : ℕ} (B : Matrix (Fin n) (Fin n) K) (c b : (Fin n→K)) (k : ℕ) : (Fin n→K) :=
  -transMat B (fun i=>b i*(1-c i^k)) +
    (fun i=>b i*((1-c i)-(1-c i^(k+1))/((k+1:ℕ):K)))

theorem gather_adjoint_by_row_difference {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (hD1 : firstSeed A b=0) (hEnd : nodes A 11=1)
    (rep : Fin 12→Fin 10) (hRep : ∀ i, rep (lowPrefix10 i)=i)
    (hNode : ∀ i, nodes A i=nodes A (lowPrefix10 (rep i))) (k : ℕ) :
    gatherRow rep (orderAdjoint A b k) =
      lateResidual (prefixMat10 A) (nodes A ∘ lowPrefix10) (gatherRow rep b) k -
        (b 10*(1-nodes A 10^k)) • (fun i =>
          A 10 (lowPrefix10 i)-A (lowPrefix10 (rep 10)) (lowPrefix10 i)) := by
  rw [orderAdjoint_of_D1 hD1,map_add,map_neg,
    gather_transMat_ten ha rep hRep _ (by simp [hEnd]),
    gather_multiply_by_nodes rep hNode b (fun x => 1-x^k),
    gather_multiply_by_nodes rep hNode b (fun x => (1-x)-(1-x^(k+1))/((k+1:ℕ):K)),
    lateResidual]
  simp only [Function.comp_apply]
  abel

theorem gather_eq_tagged {A : Matrix (Fin 12) (Fin 12) K} (rep : Fin 12→Fin 10)
    (hr : ∀ i j, rep i=rep j ↔ lowStateAt A i=lowStateAt A j)
    (hRep : ∀ i, rep (lowPrefix10 i)=i) (w : (Fin 12→K)) (i : Fin 10) :
    gatherRow rep w i=if g A (lowPrefix10 i)=0 then
      onWeight A w (nodes A (lowPrefix10 i)) else offMass A w (nodes A (lowPrefix10 i)) := by
  have h (j : Fin 12) : rep j=i ↔ lowStateAt A j=lowStateAt A (lowPrefix10 i) := by
    rw [←hr,hRep]
  by_cases hi : g A (lowPrefix10 i)=0
  · rw [gatherRow_apply,ite_eq_left hi,onWeight]
    apply Finset.sum_congr rfl
    intro j _
    simp [h j,lowState_eq_iff,hi]
  · rw [gatherRow_apply,ite_eq_right hi,offMass]
    apply Finset.sum_congr rfl
    intro j _
    simp [h j,lowState_eq_iff,hi]

theorem gather_annih_restricted {A : Matrix (Fin 12) (Fin 12) K} (rep : Fin 12→Fin 10)
    (h : ∀ i, lowStateAt A i=lowStateAt A (lowPrefix10 (rep i)))
    (U : Submodule K ((Fin 12→K))) (hU : U≤onOffSpace A)
    {w : (Fin 12→K)} (hw : w∈annih U) :
    gatherRow rep w∈annih (U.map (RKCert.Paired.restrictCol lowPrefix10)) := by
  apply mem_annih.mpr
  rintro _ ⟨v,hv,rfl⟩
  rw [gatherRow_pair]
  have he : RKCert.Paired.restrictCol lowPrefix10 v∘rep=v := by
    ext i
    change v (lowPrefix10 (rep i))=v i
    exact (onOffSpace_eq_at_states (h i) (hU hv)).symm
  rw [he]
  exact mem_annih.mp hw _ hv

theorem finrank_restrict_state {A : Matrix (Fin 12) (Fin 12) K} (rep : Fin 12→Fin 10)
    (h : ∀ i, lowStateAt A i=lowStateAt A (lowPrefix10 (rep i)))
    (U : Submodule K ((Fin 12→K))) (hU : U≤onOffSpace A) :
    finrank K (U.map (RKCert.Paired.restrictCol lowPrefix10))=finrank K U := by
  let f := (RKCert.Paired.restrictCol lowPrefix10).comp U.subtype
  have hI : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    ext i
    have hp := congrFun he (rep i)
    exact (onOffSpace_eq_at_states (h i) (hU x.property)).trans
      (hp.trans (onOffSpace_eq_at_states (h i) (hU y.property)).symm)
  have hF := LinearMap.finrank_range_of_inj hI
  rw [show f=(RKCert.Paired.restrictCol lowPrefix10).comp U.subtype from rfl,
    LinearMap.range_comp,Submodule.range_subtype] at hF
  exact hF
end RKResearch.Certified.Graded.MultiOff
