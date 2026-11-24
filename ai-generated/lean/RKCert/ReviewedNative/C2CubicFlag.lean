module

public import RKCert.ReviewedNative.DIRKForwardRank
public import RKCert.ReviewedNative.FiniteOrderCheck

@[expose] public section

/-! # The exact cubic defect flag under C(2)
No rank-budget or order assumption enters the span calculation. The
five planar order-four constructors represent only two possible native
columns when twice A c is c squared. -/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree Module
open scoped FiniteRootedTree Matrix
variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The entire grade-three ordinary defect space is the single cubic
stage defect when the quadratic defect vanishes. This is a span identity
over the coefficient ring, including rings of small characteristic. -/
theorem zeroSpace_three_of_C2 (A : Matrix ι ι R) (c₂ : monomialStageDefect A 1=0) :
    zeroSpace A 3 = R ∙ monomialStageDefect A 2 := by
  let t2 : FiniteRootedTree := .leaf ◂ .leaf
  let u := (.leaf ◂ t2)
  let v := (t2 ◂ .leaf)
  let c := nodes A
  let z := monomialStageDefect A 2
  have two : (2:R) • mat A c = c^2 := by
    ext i
    have e := congrFun c₂ i
    change (2:R) * (A *ᵥ (nodes A)^1) i - (nodes A i)^2 = 0 at e
    rwa [pow_one,sub_eq_zero] at e
  have zdef : z = (3:R) • mat A (c^2) - c^3 := rfl
  have t2val : normTree A t2=c := by
    change normTree A (.leaf ◂ .leaf)=nodes A
    rw [normTree_clock,normTree_leaf]
    ext i; simp
  have uval : normTree A u=c^2 := by
    rw [show u=.leaf ◂ t2 from rfl,normTree_unary,t2val]
    exact two
  have vval : normTree A v=c^2 := by
    rw [show v=t2 ◂ .leaf from rfl,normTree_clock,t2val]
    change c*c=c^2
    rw [pow_two]
  have fourU (t : FiniteRootedTree) (size : (t.order:ℕ)=3) (val : normTree A t=c^2) :
      normTree A (.leaf ◂ t)=(3:R) • mat A (c^2) := by
    rw [normTree_unary,size,val]
    rfl
  have fourC (t : FiniteRootedTree) (val : normTree A t=c^2) : normTree A (t ◂ .leaf)=c^3 := by
    rw [normTree_clock,val]
    change c*c^2=c^3
    exact (pow_succ' c 2).symm
  have swap : normTree A (t2 ◂ t2) = normTree A (u ◂ .leaf) := by
    change normTree A ((.leaf ◂ .leaf) ◂ t2) = normTree A ((.leaf ◂ t2) ◂ .leaf)
    unfold normTree
    rw [Φ_branch_swap .leaf .leaf t2]
    congr 1
  have contrib (t : FiniteRootedTree) (n : ℕ) (ht : (t.order:ℕ)=n+1) (hn : n≤3) :
      normTree A t-c^n∈ R ∙ z := by
    have listT := (mem_treesOfOrderSucc n t).mpr ht
    have base {x : ι→R} : x-x∈ R ∙ z := by simp
    rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl|rfl|rfl|rfl
    · have e : t=.leaf := by simpa [treesOfOrderSucc] using listT
      simp [e]
    · have e : t=t2 := by simpa [t2,treesOfOrderSucc,List.finRange_succ] using listT
      simp [e,t2val]
    · have e : t=u ∨ t=v := by simpa [t2,u,v,treesOfOrderSucc,List.finRange_succ] using listT
      rcases e with rfl|rfl <;> simp [uval,vval]
    · have e : t=.leaf ◂ u ∨ t=.leaf ◂ v ∨ t=t2 ◂ t2 ∨ t=u ◂ .leaf ∨ t=v ◂ .leaf := by
        simpa [t2,u,v,treesOfOrderSucc,List.finRange_succ] using listT
      have mem : (3:R) • mat A (c^2) - c^3 ∈ R ∙ z := (zdef ▸ Submodule.mem_span_singleton_self z)
      rcases e with rfl|rfl|rfl|rfl|rfl
      · rwa [fourU _ rfl uval]
      · rwa [fourU _ rfl vval]
      · rw [swap,fourC _ uval]; exact base
      · rw [fourC _ uval]; exact base
      · rw [fourC _ vval]; exact base
  apply le_antisymm _ ((Submodule.span_singleton_le_iff_mem ..).mpr (monomialStageDefect_mem A 2))
  apply Submodule.span_le.mpr
  rintro _ ⟨t,v,e,ht,rfl⟩
  let n : ℕ := (t.order:ℕ)-1
  have hn : (t.order:ℕ)=n+1 := by have := t.order.pos; dsimp [n]; omega
  have hn' : n≤3 := by dsimp [n]; omega
  have diff := (R ∙ z).sub_mem (contrib t n hn hn') (contrib v n (e ▸ hn) hn')
  change normTree A t - normTree A v ∈ R ∙ z
  simpa only [sub_sub_sub_cancel_right] using diff

/-- In native DIRK at attained order >=3 the nonzero direction in the
C(2) branch is exactly the cubic one. -/
theorem dirk_grade_three_of_C2 {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder A b p) (pay : 3≤p)
    (c₂ : monomialStageDefect A 1=0) :
    monomialStageDefect A 2≠0 ∧ finrank K (zeroSpace A 3)=1 := by
  have lo := (dirk_forward_rank_three ha ho pay).1
  rw [zeroSpace_three_of_C2 A c₂] at lo ⊢
  have nz : monomialStageDefect A 2≠0 := by
    intro h
    simp [h] at lo
  exact ⟨nz,finrank_span_singleton nz⟩

end RKResearch.Certified.Graded
