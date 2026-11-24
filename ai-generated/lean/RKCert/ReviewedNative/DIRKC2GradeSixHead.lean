module

public import RKCert.ReviewedNative.C2CubicFlag
public import RKCert.ReviewedNative.DIRKGradeSixHeads

@[expose] public section

/-! # The early C(2) branch has the actual cubic defect as its sole head -/
namespace RKResearch.Certified.Graded

open Polynomial RKCert.OneEscape Module
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K}
variable {b : Fin s → K}

/-- No unspecified core or normalisation remains here: the actual cubic
defect generates the length 1,2,3,4 clock chains in F3,F4,F5,F6.
This uses C(2) and the non-invariant early branch; it does not equate
C(2) with clock invariance, nor does it exclude this branch. -/
theorem dirk_grade_six_C2_early_cubic_profile
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 7≤p)
    (c₂ : monomialStageDefect A 1=0)
    (bad : ¬ finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6))
    (esc : ¬ (zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3) :
    ∃ P : K[X], P≠0 ∧ P.natDegree≤3 ∧
      4 < (HeadFiber.physicalSites (nodes A) (monomialStageDefect A 2)).card ∧
      (∀ i, monomialStageDefect A 2 i≠0 → monomialStageDefect A 2 i=P.eval (nodes A i)) ∧
      ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ (monomialStageDefect A 2) (1+k) := by
  classical
  obtain ⟨r,U,w,P,pos,inv,sub,_,_,count,band,nz,deg,fit⟩ := dirk_grade_six_head_at_three ha ho pay bad esc
  have rank := (dirk_grade_three_of_C2 ha ho (by omega) c₂).2
  have strict : U < zeroSpace A 3 := lt_of_le_of_ne sub (fun eq => esc (eq ▸ inv))
  have du := Submodule.finrank_lt_finrank_of_lt strict
  have bot : U=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  subst U
  have eq3 : zeroSpace A 3 = chain (diag (nodes A)) ⊥ w r := by simpa using band 0 (by decide)
  have paid (t : ℕ) (ht : t<r) : (diag (nodes A)^t) w∈zeroSpace A 3 := ((clock_chain_le_iff r).mp eq3.ge).2 t ht
  have hw : w∈zeroSpace A 3 := by simpa using paid 0 pos
  have wn : w≠0 := by
    intro w0
    simp [HeadFiber.physicalSites,w0] at count
  have span : K ∙ w = zeroSpace A 3 := Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem ..).mpr hw) ((finrank_span_singleton wn).trans rank.symm)
  have rr : r=1 := by
    by_contra no
    apply esc
    have cw : diag (nodes A) w∈zeroSpace A 3 := by simpa using paid 1 (by omega)
    conv_lhs => rw [←span]
    rw [Submodule.map_span,Set.image_singleton,Submodule.span_singleton_le_iff_mem]
    exact cw
  subst r
  rw [zeroSpace_three_of_C2 A c₂] at hw
  obtain ⟨t,scale⟩ := Submodule.mem_span_singleton.mp hw
  have tn : t≠0 := by intro h; apply wn; simpa [h] using scale.symm
  have sites : HeadFiber.physicalSites (nodes A) w = HeadFiber.physicalSites (nodes A) (monomialStageDefect A 2) := by
    rw [←scale]
    simp [HeadFiber.physicalSites,Pi.smul_apply,smul_eq_mul,tn]
  have same (n : ℕ) : chain (diag (nodes A)) ⊥ w n=chain (diag (nodes A)) ⊥ (monomialStageDefect A 2) n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [chain,chain,ih,←scale,map_smul,Submodule.span_singleton_smul_eq tn.isUnit]
  refine ⟨C t⁻¹*P,mul_ne_zero (C_ne_zero.mpr (inv_ne_zero tn)) nz,(natDegree_C_mul_le _ _).trans (by omega),
    sites ▸ count,?_,fun k hk => (band k hk).trans (same _)⟩
  intro i hi
  have eq : t*monomialStageDefect A 2 i=w i := congrFun scale i
  have nzi : w i≠0 := eq ▸ mul_ne_zero tn hi
  rw [eval_mul,eval_C,←fit i nzi,←eq,←mul_assoc,inv_mul_cancel₀ tn,one_mul]

end RKResearch.Certified.Graded
