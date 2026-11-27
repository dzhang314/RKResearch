module
public import RKCert.Research.SDIRKSevenEightStageF19Verification
public import RKCert.Research.SDIRKSevenEightStageF19Prelude

@[expose] public section
namespace RKResearch.Certified.SDIRKSeven.F19

open RKResearch Certified.Graded
open scoped BigOperators Matrix

/-- Excludes any normalized chart in the validated receipt list. The
external exact coverage replay supplies list membership and nonzero T. -/
theorem forbid_receipted_profile (k : Key) (a b : K) (weights : Fin 8→K)
    (ht : t k≠0) (found : (receipts k.z).any (fun s => decide (s.1=k))=true)
    (hl : l k=a*t k) (hr : r k=b*t k)
    (hquad : quadrature (Z k) (nodes k a b) weights) (hm : mask weights)
    (g4 g5 g8 : K) (hs : firstSeedLaw k (nodes k a b) weights g4 g5 g8) : False := by
  have ha : a=l k/t k := (eq_div_iff ht).mpr hl.symm
  have hb : b=r k/t k := (eq_div_iff ht).mpr hr.symm
  subst a
  subst b
  obtain ⟨item,hin,he⟩ := List.any_eq_true.mp found
  have eq : item.1=k := of_decide_eq_true he
  have valid : (receipts k.z).all (fun s => decide (F19.valid s.1 s.2))=true :=
    finite_validity k.z
  have hv := of_decide_eq_true (List.all_eq_true.mp valid _ hin)
  rw [eq] at hv
  exact prohibit_of_valid k item.2 hv weights hquad hm g4 g5 g8 hs

/-- A genuine reviewed tableau cannot satisfy the stated certified
chronological chart. Membership and middle-clock regularity are explicit
rather than silently assumed to be kernel-checked from HasOrder. -/
theorem no_reviewed_order_with_receipted_chart
    {A : Matrix (Fin 8) (Fin 8) K} {weights : Fin 8→K} {γ : K}
    (ho : HasOrder 7 A weights) (ha : A.IsLowerTriangular)
    (he : ∀i,A i i=γ) (hγ : γ≠0)
    (k : Key) (a b g4 g5 g8 : K)
    (ht : t k≠0) (found : (receipts k.z).any (fun s => decide (s.1=k))=true)
    (hl : l k=a*t k) (hr : r k=b*t k)
    (hclock : Graded.nodes (SDIRKSix.scaleTable (Z k) A)=nodes k a b)
    (hseed : SDIRKSix.seed (SDIRKSix.scaleTable (Z k) A)=seed k g4 g5 g8) : False := by
  have qd := actual_quad ho (Z k)
  rw [hclock] at qd
  apply forbid_receipted_profile k a b weights ht found hl hr qd (actual_mask ho ha he hγ) g4 g5 g8
  intro j
  have e := actual_first_seed_moments ho (Z k) j
  rw [hclock,hseed] at e
  exact e

end RKResearch.Certified.SDIRKSeven.F19
