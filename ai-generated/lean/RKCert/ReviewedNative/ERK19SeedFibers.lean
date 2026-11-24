module

public import RKCert.ReviewedNative.ERK19ReverseCover

@[expose] public section

/-! # Balanced numerical fibres of the first positive-rank reverse seed

The seed is allowed to have either sign at every physical stage. With at
most eighteen distinct touched clocks, exact moments force the *sum* of
its coefficients at every such clock to vanish. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

def clockMass (c v : Fin s→K) (a : K) : K :=
  ∑ i ∈ Finset.univ.filter (fun i => c i=a), v i

theorem weighted_sum_by_clock (c v : Fin s→K) (R : K→K) :
    (∑ i, v i * R (c i)) = ∑ a ∈ Finset.univ.image c, clockMass c v a * R a := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s:=Finset.univ) (t:=Finset.univ.image c) (g:=c)
    (fun i hi => Finset.mem_image_of_mem c hi) (fun i => v i * R (c i))]
  apply Finset.sum_congr rfl
  intro a _
  rw [clockMass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem clockMass_zero_of_not_site {c v : Fin s→K} {a : K}
    (absent : a∉weightedSites c v) : clockMass c v a=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_contra nz
  exact absent (mem_weightedSites.mpr ⟨i,nz,(Finset.mem_filter.mp hi).2⟩)

/-- The same numerical affine change of clock on both sites and evaluations. -/
theorem first_seed_site_card_eq :
    (weightedSites (reflectedClock A) (firstSeed A b)).card =
      (weightedSites (nodes A) (firstSeed A b)).card := by
  have eq : weightedSites (reflectedClock A) (firstSeed A b) =
      (weightedSites (nodes A) (firstSeed A b)).image (fun x=>1-x) := by
    ext z
    rw [mem_weightedSites,Finset.mem_image]
    constructor
    · rintro ⟨i,hi,e⟩
      exact ⟨nodes A i,mem_weightedSites.mpr ⟨i,hi,rfl⟩,e⟩
    · rintro ⟨r,hr,e⟩
      obtain ⟨i,hi,v⟩ := mem_weightedSites.mp hr
      exact ⟨i,hi,by change 1-nodes A i=z; rwa [v]⟩
  rw [eq,Finset.card_image_of_injective]
  intro x y e
  exact (sub_right_inj (a:=1)).mp e

/-- Form the ordinary seed moment test using the actual output row,
not an auxiliary reverse tableau. -/
theorem first_seed_clockMass_zero (ho : HasOrder p A b)
    (enough : (weightedSites (nodes A) (firstSeed A b)).card + 1 ≤ p) :
    ∀ a, clockMass (nodes A) (firstSeed A b) a=0 := by
  let c := nodes A
  let d := firstSeed A b
  let T := weightedSites c d
  intro a
  by_cases atT : a∈T
  · let P := Lagrange.basis T id a
    have degree : P.natDegree+2≤p := by
      have e := Lagrange.natDegree_basis (Set.injOn_id _) atT
      have h := Finset.card_pos.mpr ⟨a,atT⟩
      change P.natDegree = T.card-1 at e
      change T.card+1≤p at enough
      omega
    have dm : d∈primitiveBack A b 0 := Submodule.mem_span_singleton_self _
    have test := mem_annih.mp
      (primitiveBack_annih ho P.natDegree 0 (by omega) dm) _ (evalNodes_mem_treeSpace A P le_rfl)
    change (∑i, d i*P.eval (c i))=0 at test
    have eq : (∑i, d i*P.eval (c i))=clockMass c d a := by
      rw [weighted_sum_by_clock c d (fun x => P.eval x)]
      have ai : a∈Finset.univ.image c := by
        obtain ⟨i,_,e⟩ := mem_weightedSites.mp atT
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e⟩
      rw [Finset.sum_eq_single_of_mem a ai]
      · rw [show P.eval a=1 from Lagrange.eval_basis_self (Set.injOn_id _) atT,mul_one]
      · intro q _ qne
        by_cases qt : q∈T
        · rw [show P.eval q=0 from Lagrange.eval_basis_of_ne (v:=id) qne.symm qt,mul_zero]
        · rw [clockMass_zero_of_not_site qt,zero_mul]
    exact eq ▸ test
  · exact clockMass_zero_of_not_site atT

end
end RKResearch.Certified.Graded.Reverse

namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

def FullFirstBand (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K) : Prop :=
  annih (treeSpace A 9) = weightedBand (reflectedClock A) (firstSeed A b) 9

def OriginalFirstCarrier (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K) :
    Submodule K (Fin 29→K) := (weightedEval (nodes A) (firstSeed A b)).range

theorem FullFirstBand.represent (band : FullFirstBand A b) {v : Fin 29→K}
    (hv : v∈annih (treeSpace A 9)) : v∈OriginalFirstCarrier A b := by
  rw [band] at hv
  obtain ⟨P,_,eq⟩ := mem_weightedBand.mp hv
  refine ⟨P.comp (1-X),?_⟩
  ext i
  have e := congrFun eq i
  simpa only [weightedEval_apply,eval_comp,eval_sub,eval_one,eval_X,reflectedClock,
    Pi.sub_apply,Pi.one_apply] using e

theorem first_seed_mixed_annih (ho : HasOrder 19 A b) {j k : ℕ} (pay : j+k≤17)
    {v : Fin 29→K} (hv : v∈treeSpace A j) :
    firstSeed A b*v∈annih (treeSpace A k) := by
  refine mem_annih.mpr fun w hw => ?_
  have seed : firstSeed A b∈primitiveBack A b 0 := Submodule.mem_span_singleton_self _
  have a := mem_annih.mp (primitiveBack_annih ho (j+k) 0 (by omega) seed) _
    (treeSpace_mul hv hw)
  simpa only [row_apply,dotProduct,Pi.mul_apply,mul_assoc] using a

theorem weight_defect_mixed_annih (ho : HasOrder 19 A b) {j k : ℕ} (pay : j+k≤18)
    {v : Fin 29→K} (hv : v∈zeroSpace A j) : b*v∈annih (treeSpace A k) := by
  refine mem_annih.mpr fun w hw => ?_
  have a := probe_zeroSpace (k:=0) ho (by omega) (zeroSpace_mul_treeSpace ho (by omega) hv hw)
  have e : probe A b 0 (v*w) = 0 := a
  simpa only [probe,row_apply,dotProduct,Pi.mul_apply,pow_zero,mul_one,mul_assoc] using e

/-- Actual derivative rows through tree order nine agree within each
nonzero-seed numerical fibre. No grade-nine equality is inferred here. -/
theorem first_seed_fibre_tree_eight (ho : HasOrder 19 A b) (band : FullFirstBand A b)
    {v : Fin 29→K} (hv : v∈treeSpace A 8) {i j : Fin 29}
    (di : firstSeed A b i≠0) (dj : firstSeed A b j≠0) (same : nodes A i=nodes A j) :
    v i=v j := by
  obtain ⟨Q,e⟩ := band.represent (first_seed_mixed_annih ho (j:=8) (k:=9) (by decide) hv)
  have a (k : Fin 29) (nz : firstSeed A b k≠0) : v k=Q.eval (nodes A k) := by
    have h := congrFun e k
    exact (mul_right_inj' nz).mp (by simpa only [weightedEval_apply,Pi.mul_apply,mul_comm] using h.symm)
  rw [a i di,a j dj,same]

theorem first_carrier_rank :
    finrank K (OriginalFirstCarrier A b) = (weightedSites (nodes A) (firstSeed A b)).card := by
  let m := (weightedSites (nodes A) (firstSeed A b)).card
  rw [OriginalFirstCarrier,←weightedBand_eq_range (nodes A) (firstSeed A b) m le_rfl]
  exact weightedBand_rank _ _ _ le_rfl

/-- The whole clock-localized seed carrier annihilates E8, not just the
already paid degree-eight polynomial slice, whenever every local mass
vanishes. This is independent of chronology and ordering. -/
theorem balanced_first_carrier_le_annih_eight (ho : HasOrder 19 A b)
    (band : FullFirstBand A b) (balance : ∀ a, clockMass (nodes A) (firstSeed A b) a=0) :
    OriginalFirstCarrier A b ≤ annih (treeSpace A 8) := by
  rintro _ ⟨P,rfl⟩
  refine mem_annih.mpr fun v hv => ?_
  obtain ⟨Q,e⟩ := band.represent (first_seed_mixed_annih ho (j:=8) (k:=9) (by decide) hv)
  calc
    row (weightedEval (nodes A) (firstSeed A b) P) v =
        ∑ i, firstSeed A b i*(P.eval (nodes A i)*Q.eval (nodes A i)) := by
      simp only [row_apply,dotProduct,weightedEval_apply]
      apply Finset.sum_congr rfl
      intro i _
      have h := congrFun e i
      simp only [weightedEval_apply,Pi.mul_apply] at h
      calc
        P.eval (nodes A i)*firstSeed A b i*v i =
            P.eval (nodes A i)*(firstSeed A b i*v i) := by ring
        _ = _ := by rw [←h]; ring
    _ = 0 := by
      rw [weighted_sum_by_clock (nodes A) (firstSeed A b) (fun x => P.eval x * Q.eval x)]
      simp only [balance,zero_mul,Finset.sum_const_zero]

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem width29_annih_eight_rank (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b) :
    finrank K (annih (treeSpace A 8))=11 := by
  have h := treeSpace_rank_eq_of_separation ho (q:=8) (by decide) (coeff_separated ho (by decide))
  rw [(width29_eight_nine ha ho).1] at h
  have a := finrank_annih (treeSpace A 8)
  rw [Fintype.card_fin] at a
  omega

/-- Combined with the prior wide-or-local dichotomy, a first seed of
at most eighteen sites is either local (at most two) or has exactly
ten or eleven sites. The other medium sizes are genuinely excluded. -/
theorem width29_first_seed_not_twelve_through_eighteen (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (small : (weightedSites (reflectedClock A) (firstSeed A b)).card≤18) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card≤2 ∨
      ((weightedSites (reflectedClock A) (firstSeed A b)).card=10 ∨
       (weightedSites (reflectedClock A) (firstSeed A b)).card=11) := by
  rcases width29_nonzero_broad_or_local ha ho nz with loc|⟨wide,band⟩
  · exact Or.inl loc
  have eq := first_seed_site_card_eq (A:=A) (b:=b)
  have balance := first_seed_clockMass_zero ho (by omega)
  have cap := Submodule.finrank_mono (balanced_first_carrier_le_annih_eight ho band balance)
  rw [first_carrier_rank, width29_annih_eight_rank ha ho] at cap
  exact Or.inr (by omega)

end
end RKResearch.Certified.ERK19
