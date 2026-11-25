module

public import RKCert.ReviewedNative.AffineReceiverLowerPrefix
public import RKCert.ReviewedNative.OffReceiverEffectiveDonors

@[expose] public section

/-! # Earlier effective clocks after removing the entire receiver fibre -/
namespace RKResearch.Certified.Graded

open RKResearch EffectiveDonors
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {l : Fin s→K}
variable {x : K} {cut : Fin s}

/-- The inclusive lower prefix pays a count strictly before the last
live receiver, grouped by original clocks in the literal combined row.
Shift zero allows clock zero; shift one removes it. -/
theorem ClockAffineProbe.lower_offReceiver_donor_count (P : ClockAffineProbe A l x cut)
    (lower : ∀ i j,i<j→A i j=0) (nz : x≠0) (lastLive : l cut≠0)
    (q : ℕ) (paid : ∀ v∈zeroSpace A q, row l v=0)
    {n e : ℕ} (budget : 2*n+e≤q) :
    n≤(offReceiverSites
      (fun j : Fin cut.val=>nodes A (Fin.castLE cut.isLt.le j))
      (fun j : Fin cut.val=>affineReceiverRow A l (Fin.castLE cut.isLt.le j)) x e).card := by
  classical
  let hk : cut.val+1≤s := Nat.succ_le_of_lt cut.isLt
  let a := x⁻¹
  let B := prefixMatrix A hk
  let c : Fin (cut.val+1)→K := fun j=>nodes A (Fin.castLE hk j)
  let w : Fin (cut.val+1)→K := fun j=>affineReceiverRow A l (Fin.castLE hk j)
  let D := offReceiverSites c w x e
  have an : a≠0 := inv_ne_zero nz
  have ax : a*x=1 := inv_mul_cancel₀ nz
  have liveClock : c (Fin.last cut.val)=x := by
    change nodes A (Fin.castLE hk (Fin.last cut.val))=x
    rw [show Fin.castLE hk (Fin.last cut.val)=cut from Fin.ext rfl]
    exact P.atClock cut lastLive
  have pref : HasOrder q (a • B) (fun j=>a*w j) :=
    P.prefix_hasOrder_inclusive_of_lower lower nz q paid
  have originNodes : nodes B=c := by
    have eq := prefix_mulVec_of_lower lower hk (1:Fin s→K)
    have one : prefixRestrict hk (1:Fin s→K)=1 := by ext j; simp
    rw [one] at eq
    ext j
    simpa only [B,c,nodes,prefixRestrict_apply] using congrFun eq j
  have scaled : nodes (a • B)=(fun j=>a*c j) := by
    change (a • B) *ᵥ (1:Fin (cut.val+1)→K)=_
    rw [Matrix.smul_mulVec]
    change a • nodes B=_
    rw [originNodes] <;> rfl
  have cap : n≤(D.image (fun u=>a*u)).card := by
    apply off_one_cover_card_of_hasOrder pref budget
    intro y occupied y1 yp outside
    obtain ⟨i,ei⟩ := occupied
    rw [scaled] at ei
    change a*c i=y at ei
    have ci : c i≠x := fun eq=>y1 (by rw [←ei,eq,ax])
    have cp : (c i)^e≠0 := fun eq=>yp (by rw [←ei,mul_pow,eq,mul_zero])
    have massZero : clockMass c w (c i)=0 := by
      by_contra live
      have mem : c i∈D := mem_offReceiverSites.mpr ⟨⟨i,rfl⟩,ci,cp,live⟩
      exact outside (Finset.mem_image.mpr ⟨c i,mem,ei⟩)
    rw [scaled,←ei,clockMass_scale c w an a (c i),massZero,mul_zero]
  have count : n≤D.card := cap.trans Finset.card_image_le
  change n≤(offReceiverSites (fun j : Fin cut.val=>c j.castSucc)
    (fun j : Fin cut.val=>w j.castSucc) x e).card
  rw [←offReceiverSites_remove_last c w liveClock e]
  exact count

end
end RKResearch.Certified.Graded
