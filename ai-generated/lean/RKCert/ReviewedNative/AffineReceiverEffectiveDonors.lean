module

public import RKCert.ReviewedNative.EffectiveDonorClocks
public import RKCert.ReviewedNative.AffineReceiverPrefix

@[expose] public section

/-! # The sign-free donor count on a literal affine prefix

The count is stated on original clocks and the original combined row,
not just their scaled versions. No rank branch or endpoint enters.
-/
namespace RKResearch.Certified.Graded

open RKResearch EffectiveDonors
open scoped Matrix
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {l : Fin s→K}
variable {x : K} {cut : Fin s}

/-- A nonzero affine receiver paid through order q has at least q/2
distinct earlier nonzero clocks with a nonzero aggregate in its
literal unscaled combined row. -/
theorem ClockAffineProbe.effective_donor_count (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (nz : x≠0) (q : ℕ)
    (paid : ∀ v∈zeroSpace A q, row l v=0) :
    q/2≤(sites
      (fun j : Fin cut.val=>nodes A (Fin.castLE cut.isLt.le j))
      (fun j : Fin cut.val=>affineReceiverRow A l (Fin.castLE cut.isLt.le j))).card := by
  classical
  let a := x⁻¹
  have an : a≠0 := inv_ne_zero nz
  let B := prefixMatrix A cut.isLt.le
  let c : Fin cut.val→K := fun j=>nodes A (Fin.castLE cut.isLt.le j)
  let w : Fin cut.val→K := fun j=>affineReceiverRow A l (Fin.castLE cut.isLt.le j)
  let D := sites c w
  have pref : HasOrder q (a • B) (fun j=>a*w j) := P.prefix_hasOrder strict nz q paid
  have originNodes : nodes B=c := by
    have eq := prefix_mulVec strict cut.isLt.le (1:Fin s→K)
    have one : prefixRestrict cut.isLt.le (1:Fin s→K)=1 := by ext j; simp
    rw [one] at eq
    ext j
    simpa only [B,c,nodes,prefixRestrict_apply] using congrFun eq j
  have scaled : nodes (a • B)=(fun j=>a*c j) := by
    change (a • B) *ᵥ (1:Fin cut.val→K)=_
    rw [Matrix.smul_mulVec]
    change a • nodes B=_
    rw [originNodes] <;> rfl
  have cap : q/2≤(D.image (fun u=>a*u)).card := by
    apply cover_card_of_hasOrder pref
    intro y occupied yn outside
    obtain ⟨i,eq⟩ := occupied
    rw [scaled] at eq
    change a*c i=y at eq
    have cn : c i≠0 := fun h=>yn (by rw [←eq,h,mul_zero])
    have massZero : clockMass c w (c i)=0 := by
      by_contra live
      have mem : c i∈D := mem_sites.mpr ⟨⟨i,rfl⟩,cn,live⟩
      exact outside (Finset.mem_image.mpr ⟨c i,mem,eq⟩)
    rw [scaled,←eq,clockMass_scale c w an a (c i),massZero,mul_zero]
  exact cap.trans Finset.card_image_le

end
end RKResearch.Certified.Graded
