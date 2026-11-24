module

public import RKCert.ReviewedNative.ERKOrder16EightSites

@[expose] public section

/-! # The original terminal-deleted seventh reverse horizon at width 24

In the full F7 branch, the seventh paid quadratic seed power exhausts
the marked annihilator. The shared eight-site lower bound then
allows the true two traces of every grade-five head to refund degrees. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

structure Width24StrongCover [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K) : Prop where
  quadratic : Width24QuadraticCover A b
  sites : 8≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card
  band : zeroAt (annih (treeSpace A 7)) (Fin.last 23) =
    weightedBand (reflectedClock A) (quadraticSeed A b) 7

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem width24_strong_reverse_cover_of_quadratic
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (C : Width24QuadraticCover A b) (f7 : finrank K (zeroSpace A 7)=8) :
    Width24StrongCover A b := by
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let L := primitiveBack A b
  let U := zeroAt (annih (treeSpace A 7)) t
  have tr7 := erk_midpoint_tree_rank ha ho (q:=7) (by decide) (by decide)
  have ar7 := finrank_annih (treeSpace A 7)
  rw [Fintype.card_fin,tr7,f7] at ar7
  have ur : finrank K U=7 := by
    have e := finrank_zeroAt_annih (treeSpace A 7) t C.frame.lastOut
    change finrank K U+1=_ at e
    omega
  have v7 : L 7≤U := by
    intro v hv
    exact mem_zeroAt.mpr ⟨primitiveBack_annih ho 7 7 (by decide) hv,
      (mem_tailZero.mp (C.frame.lastLive.primitiveBack_tail ha C.frame.seedZero 7 hv)) t le_rfl⟩
  have sd : d∈L 1 := adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have wb : weightedBand y d 7≤L 7 := weighted_band_of_primitive_seed sd 6
  have wr := weightedBand_rank y d 7 C.sites
  have wu : weightedBand y d 7=U := by
    apply Submodule.eq_of_le_of_finrank_le (wb.trans v7)
    rw [wr,ur]
  exact ⟨C,width24_quadratic_eight_sites ha ho,wu.symm⟩

theorem width24_strong_reverse_cover (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (f7 : finrank K (zeroSpace A 7)=8) :
    Width24StrongCover A b :=
  width24_strong_reverse_cover_of_quadratic ha ho (width24_quadratic_cover ha ho) f7

theorem Width24StrongCover.poly_cover (C : Width24StrongCover A b)
    {v : Fin 24 → K} (hv : v∈zeroAt (annih (treeSpace A 7)) (Fin.last 23)) :
    ∃ R : K[X], R.natDegree≤6 ∧ weightedEval (reflectedClock A) (quadraticSeed A b) R=v := by
  rw [C.band] at hv
  obtain ⟨R,rd,e⟩ := mem_weightedBand.mp hv
  refine ⟨R,?_,e⟩
  by_cases hz:R=0
  · simp [hz]
  · have k : R.natDegree<7 := (natDegree_lt_iff_degree_lt hz).mpr rd
    omega

theorem Width24StrongCover.supports (C : Width24StrongCover A b) :
    Thin.SupportsComplement A b 7 (Fin.last 23) :=
  Thin.supportsComplement_of_cover (h:=6) (fun _ hv=>C.poly_cover hv)

theorem Width24StrongCover.two_traces (C : Width24StrongCover A b)
    (ho : HasOrder 16 A b) {f : Fin 24 → K} (hf : f∈zeroSpace A 5) :
    ∃ Q P : K[X], Q.natDegree≤5 ∧ P.natDegree≤4 ∧
      (∀i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i) ∧
      (∀i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i) := by
  have yz : reflectedClock A (Fin.last 23)=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [C.quadratic.frame.lastClock,sub_self]
  exact Thin.thin_reverse_two_traces ho hf (by decide) (h:=6) (m:=7) (by decide) (by decide)
    (Fin.last 23) yz C.quadratic.lastSeed (by exact C.sites) (fun _ hv=>C.poly_cover hv)

end
end RKResearch.Certified.ERK16
