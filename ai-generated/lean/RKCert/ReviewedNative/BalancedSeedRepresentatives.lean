module

public import RKCert.ReviewedNative.ERK19SeedReceivers
public import RKCert.ReviewedNative.CausalMerge

@[expose] public section

/-! # First representatives in the original physical stage order -/
namespace RKResearch.Certified.Graded.Reverse
open RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}

def seedFibre (c d : Fin s→K) (x : K) : Finset (Fin s) :=
  Finset.univ.filter (fun i=>d i≠0 ∧ c i=x)

theorem mem_seedFibre {c d : Fin s→K} {x : K} {i : Fin s} :
    i∈seedFibre c d x ↔ d i≠0 ∧ c i=x := by simp [seedFibre]

def seedRep (c d : Fin s→K) (i : Fin s) : Fin s :=
  if h : d i≠0 then (seedFibre c d (c i)).min' ⟨i,mem_seedFibre.mpr ⟨h,rfl⟩⟩ else i

theorem seedRep_of_dead {c d : Fin s→K} {i : Fin s} (h : d i=0) :
    seedRep c d i=i := by simp [seedRep,h]

theorem seedRep_live {c d : Fin s→K} {i : Fin s} (h : d i≠0) :
    d (seedRep c d i)≠0 ∧ c (seedRep c d i)=c i := by
  rw [seedRep,dite_eq_left h]
  exact mem_seedFibre.mp (Finset.min'_mem _ _)

theorem seedRep_le (c d : Fin s→K) (i : Fin s) : seedRep c d i ≤ i := by
  by_cases h : d i≠0
  · rw [seedRep,dite_eq_left h]
    exact Finset.min'_le _ _ (mem_seedFibre.mpr ⟨h,rfl⟩)
  · exact (seedRep_of_dead (c:=c) (not_not.mp h)).le

theorem seedRep_eq_of_live {c d : Fin s→K} {i j : Fin s}
    (hi : d i≠0) (hj : d j≠0) (same : c i=c j) :
    seedRep c d i=seedRep c d j := by
  simp [seedRep,hi,hj,same]

theorem seedRep_idempotent (c d : Fin s→K) (i : Fin s) :
    seedRep c d (seedRep c d i)=seedRep c d i := by
  by_cases h : d i≠0
  · obtain ⟨nz,e⟩ := seedRep_live (c:=c) h
    exact seedRep_eq_of_live nz h e
  · simp only [seedRep_of_dead (c:=c) (not_not.mp h)]

def seedRepresentatives (c d : Fin s→K) : Finset (Fin s) :=
  Finset.univ.image (seedRep c d)

theorem mem_seedRepresentatives {c d : Fin s→K} {i : Fin s} :
    i∈seedRepresentatives c d ↔ seedRep c d i=i := by
  constructor
  · rintro hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact seedRep_idempotent _ _ _
  · intro hi
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩

/-- One actual removed row can be charged to each distinct balanced
nonzero-amplitude seed clock. This is a cardinality count, not a claim
that all later tree orders are preserved by merely matching clocks. -/
theorem balanced_seed_representative_count {c d : Fin s→K}
    (balance : ∀ a,clockMass c d a=0) :
    (seedRepresentatives c d).card + (weightedSites c d).card≤s := by
  let T := weightedSites c d
  let R := seedRepresentatives c d
  let D := Finset.univ.filter (fun i=>i∉R)
  have witness (a : T) : ∃ j : Fin s, c j=a.val ∧ j∈D := by
    obtain ⟨i,di,ci⟩ := mem_weightedSites.mp a.property
    let k := seedRep c d i
    obtain ⟨dk,ck⟩ := seedRep_live (c:=c) di
    obtain ⟨j,ne,dj,cj⟩ := balanced_clock_has_two (balance a.val) k dk (ck.trans ci)
    have r : seedRep c d j=k := seedRep_eq_of_live dj di (cj.trans ci.symm)
    refine ⟨j,cj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun jR => ne ?_⟩⟩
    exact (mem_seedRepresentatives.mp jR).symm.trans r
  choose g cg hg using witness
  let f (a : T) : D := ⟨g a,hg a⟩
  have inj : Function.Injective f := by
    intro x y eq
    apply Subtype.ext
    have e := congrArg (fun a : D => c a.val) eq
    exact (cg x).symm.trans (e.trans (cg y))
  have m := Finset.card_le_card_of_injective inj
  have h := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i=>i∈R)
  have e : Finset.univ.filter (fun i=>i∈R) = R := by ext i; simp
  rw [e,Finset.card_univ,Fintype.card_fin] at h
  change R.card + D.card = s at h
  change R.card + T.card ≤ s
  omega

end
end RKResearch.Certified.Graded.Reverse
