module

public import RKCert.ReviewedNative.ReverseUnitQuadratic
public import RKCert.ReviewedNative.ClockHeadFibers
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # An actual rank-nine reverse carrier at measured order-eighteen room

The room, zero first seed, and one-clock second seed are explicit inputs.
All flags use the original reviewed tableau, physical nodes and weights.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.OneEscape
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private theorem ordered_hermite_incoming_aux
    (ord : Fin s ≃ Fin s) (N : Module.End K (Fin s → K)) (hc : Causal ord N)
    (c v : Fin s → K) (V Z : Submodule K (Fin s → K))
    (hmask : MaskInvariant c Z) (sub : V ≤ Z) (moves : ∀ x ∈ V, N x ∈ Z) (r : ℕ)
    (count : r ≤ (failedNodes c v Z s).card)
    (paid : ∀ Q : K[X], Q.natDegree + 1 ≤ 2*r →
      N (weightedEval c v Q) - weightedEval c v (primitive Q) ∈ Z) :
    finrank K V + r ≤ finrank K Z := by
  classical
  let E : (Fin s → K) ≃ₗ[K] (Fin s → K) := LinearEquiv.funCongrLeft K K ord.symm
  let M := E.toLinearMap.comp (N.comp E.symm.toLinearMap)
  have atOrd (x : Fin s → K) (i : Fin s) : E x (ord i) = x i :=
    congrArg x (ord.symm_apply_apply i)
  have mE (x : Fin s → K) : M (E x) = E (N x) := by
    change E (N (E.symm (E x))) = _
    rw [E.symm_apply_apply]
  have chron : StrictlyCausal M := by
    intro i x y hxy
    have z := hc (ord.symm i) (E.symm x-E.symm y) (by
      intro k hk
      rw [ord.apply_symm_apply] at hk
      change x (ord k)-y (ord k)=0
      exact sub_eq_zero.mpr (hxy (ord k) hk))
    change N (E.symm x) (ord.symm i)=N (E.symm y) (ord.symm i)
    simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using z
  have mask : MaskInvariant (E c) (Z.map E.toLinearMap) := by
    rintro a _ ⟨x,hx,rfl⟩
    exact ⟨blockMask c a x,hmask a x hx,rfl⟩
  have nodes : failedNodes c v Z s ⊆
      failedNodes (E c) (E v) (Z.map E.toLinearMap) s := by
    intro a h
    obtain ⟨an,no⟩ := mem_failedNodes.mp h
    refine mem_failedNodes.mpr ⟨an,?_⟩
    rintro ⟨_,⟨x,hx,rfl⟩,matchx⟩
    apply no
    refine ⟨x,hx,fun i _ hi => ?_⟩
    have q := matchx (ord i) (ord i).isLt ((atOrd c i).trans hi)
    change E x (ord i)=E v (ord i) at q
    rwa [atOrd,atOrd] at q
  have ew (Q : K[X]) : weightedEval (E c) (E v) Q =
      E (weightedEval c v Q) := by
    ext i
    change weightedEval (E c) (E v) Q i=weightedEval c v Q (ord.symm i)
    simp only [weightedEval_apply]
    rfl
  have rank := incoming_nodal_gain (E c) (E v) (V.map E.toLinearMap)
    (Z.map E.toLinearMap) M chron mask (Submodule.map_mono sub) (by
      rintro _ ⟨x,hx,rfl⟩
      change M (E x) ∈ _
      rw [mE]
      exact Submodule.mem_map_of_mem (moves x hx)) r
    (count.trans (Finset.card_le_card nodes)) (by
      intro Q hQ
      rw [ew,ew,mE,formalPrimitive_eq_native,←map_sub]
      exact Submodule.mem_map_of_mem (paid Q hQ))
  rw [←(E.submoduleMap V).finrank_eq,←(E.submoduleMap Z).finrank_eq] at rank
  exact rank

/-- Incoming gain when the actual receiving primitive flag is clock-stable. -/
theorem primitiveBack_clock_invariant_incoming (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (n : ℕ) (pay : n + 3 ≤ p)
    (inv : (primitiveBack A b (n+1)).map (diag (reflectedClock A)) ≤
      primitiveBack A b (n+1)) :
    finrank K (primitiveBack A b n) + (n+2)/2 ≤
      finrank K (primitiveBack A b (n+1)) := by
  let V := primitiveBack A b n
  let Z := primitiveBack A b (n+1)
  let r := (n+2)/2
  have mask : MaskInvariant (reflectedClock A) Z :=
    clock_mask_invariant (fun _ hv => inv (Submodule.mem_map_of_mem hv))
  have mass (v : Fin s → K) (hv : v ∈ Z) : ∑ i,v i=0 := by
    have h := mem_annih.mp (primitiveBack_annih ho 0 (n+1) (by omega) hv) _
      (one_mem_treeSpace A 0)
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using h
  have enough := reverse_failed_clock_blocks ho Z mask mass (r:=r) (by dsimp [r]; omega)
  exact ordered_hermite_incoming_aux Fin.revPerm (mat A.transpose) (causal_transpose ha)
    (reflectedClock A) b V Z mask (adjointFlag_le_succ _ _)
    (fun _ hv => adjointFlag_transpose _ _ (Submodule.mem_map_of_mem hv))
    r enough (fun Q hQ => reverse_primitive_next n Q (by dsimp [r] at hQ; omega))

/-- A one-clock quadratic seed with vanishing first seed forces an actual
surplus by the fourth all-monomial adjoint grade. -/
theorem primitiveBack_rank_four_of_one_clock (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (pay : 10 ≤ p) (first : firstSeed A b = 0)
    (oneClock : (weightedSites (reflectedClock A) (quadraticSeed A b)).card ≤ 1) :
    5 ≤ finrank K (primitiveBack A b 4) := by
  by_contra small
  have ranks (n : ℕ) (hn : n ≤ 4) :
      finrank K (back A b n) = n ∧ back A b n = primitiveBack A b n := by
    have low := back_finrank ha ho n (by omega)
    rw [first_dim_zero first,zero_add] at low
    have inc := back_le_primitiveBack (A:=A) (b:=b) n
    have rin := Submodule.finrank_mono inc
    have step := primitiveBack_interval ha ho n (4-n) (by omega)
    rw [show n+(4-n)=4 by omega] at step
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩
  have primRank (n : ℕ) (hn : n ≤ 4) : finrank K (primitiveBack A b n) = n := by
    rw [←(ranks n hn).2]
    exact (ranks n hn).1
  have escape (n : ℕ) (lo : 2 ≤ n) (hi : n ≤ 3) :
      ¬ (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n := by
    intro inv
    have grow := reverse_clock_invariant_gain ha ho n (by omega) inv
    rw [primRank n (by omega),primRank (n+1) (by omega)] at grow
    omega
  have sites := UnitQuadratic.quadratic_sites_ge_two ha ho pay ⟨first,ranks,escape⟩
  omega

/-- At a unit rank step, an actual clock escape pays the whole next grade. -/
theorem primitiveBack_clock_step_of_unit_rank (n : ℕ)
    (rank : finrank K (primitiveBack A b (n+1)) ≤ finrank K (primitiveBack A b n)+1)
    (escape : ¬ (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n) :
    primitiveBack A b (n+1) =
      primitiveBack A b n ⊔ (primitiveBack A b n).map (diag (reflectedClock A)) := by
  let V := primitiveBack A b n
  let Y := diag (reflectedClock A)
  have inc : V ⊔ V.map Y ≤ primitiveBack A b (n+1) :=
    sup_le (adjointFlag_le_succ _ _) (adjointFlag_clock _ _)
  have strict : V < V ⊔ V.map Y := lt_of_le_of_ne le_sup_left
    (fun e => escape (le_sup_right.trans e.ge))
  have gain := Submodule.finrank_lt_finrank_of_lt strict
  exact (Submodule.eq_of_le_of_finrank_le inc (by
    change finrank K (primitiveBack A b (n+1)) ≤
      finrank K (V ⊔ V.map Y : Submodule K (Fin s → K))
    change finrank K (primitiveBack A b (n+1)) ≤ finrank K V + 1 at rank
    omega)).symm

/-- The actual reverse carrier, with the measured terminal mark retained.
The first clock window has length r; it grows by four through grade eight. -/
structure RankNineReverseCarrier (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (t : Fin s) (r : ℕ) (U : Submodule K (Fin s → K)) (w : Fin s → K) : Prop where
  reflectedZero : reflectedClock A t = 0
  tail : ∀ n, primitiveBack A b n ≤ tailZero t
  full : primitiveBack A b 8 = zeroAt (annih (treeSpace A 8)) t
  ranks : ∀ n, 4 ≤ n → n ≤ 8 → finrank K (primitiveBack A b n) = n+1
  positive : 0 < r
  stable : U.map (diag (reflectedClock A)) ≤ U
  inside : U ≤ primitiveBack A b 4
  maximal : ∀ V : Submodule K (Fin s → K),
    V.map (diag (reflectedClock A)) ≤ V → V ≤ primitiveBack A b 4 → V ≤ U
  rankSplit : finrank K U + r = 5
  chains : ∀ k, k ≤ 4 →
    primitiveBack A b (4+k) = chain (diag (reflectedClock A)) U w (r+k)
  corePos : 1 ≤ finrank K U
  coreCap : finrank K U ≤ 3
  escapeSites : r+4 < (HeadFiber.escapeSites (reflectedClock A) w U).card

/-- From explicit total room and the two actual seed conditions, produce
the full rank-nine carrier and all four intervening unit steps. -/
theorem rank_nine_reverse_carrier_of_measured_room
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 18 A b)
    {t : Fin s} (last : LastActive b t) (first : firstSeed A b = 0)
    (oneClock : (weightedSites (reflectedClock A) (quadraticSeed A b)).card = 1)
    (room : finrank K (zeroAt (annih (treeSpace A 8)) t) ≤ 9) :
    ∃ (r : ℕ) (U : Submodule K (Fin s → K)) (w : Fin s → K),
      RankNineReverseCarrier A b t r U w := by
  classical
  have surplus := primitiveBack_rank_four_of_one_clock ha ho (by decide) first oneClock.le
  have tail (n : ℕ) : primitiveBack A b n ≤ tailZero t :=
    last.primitiveBack_tail ha first n
  have inc : primitiveBack A b 8 ≤ zeroAt (annih (treeSpace A 8)) t := by
    intro v hv
    exact mem_zeroAt.mpr ⟨primitiveBack_annih ho 8 8 (by decide) hv,
      mem_tailZero.mp (tail 8 hv) t le_rfl⟩
  have upper : finrank K (primitiveBack A b 8) ≤ 9 :=
    (Submodule.finrank_mono inc).trans room
  have lower : 9 ≤ finrank K (primitiveBack A b 8) := by
    have step := primitiveBack_interval ha ho 4 4 (by decide)
    change finrank K (primitiveBack A b 4)+4 ≤ finrank K (primitiveBack A b 8) at step
    omega
  have full := Submodule.eq_of_le_of_finrank_le inc (room.trans lower)
  have ranks (n : ℕ) (lo : 4 ≤ n) (hi : n ≤ 8) :
      finrank K (primitiveBack A b n) = n+1 := by
    have firstStep := primitiveBack_interval ha ho 4 (n-4) (by omega)
    have lastStep := primitiveBack_interval ha ho n (8-n) (by omega)
    rw [show 4+(n-4)=n by omega] at firstStep
    rw [show n+(8-n)=8 by omega] at lastStep
    omega
  have escape (n : ℕ) (lo : 4 ≤ n) (hi : n < 8) :
      ¬ (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n := by
    intro inv
    have gain := reverse_clock_invariant_gain ha ho n (by omega) inv
    rw [ranks n lo (by omega),ranks (n+1) (by omega) (by omega)] at gain
    omega
  have lastEscape :
      ¬ (primitiveBack A b 8).map (diag (reflectedClock A)) ≤ primitiveBack A b 8 := by
    intro inv
    have gain := primitiveBack_clock_invariant_incoming ha ho 7 (by decide) inv
    change finrank K (primitiveBack A b 7)+4 ≤ finrank K (primitiveBack A b 8) at gain
    rw [ranks 7 (by decide) (by decide),ranks 8 (by decide) (by decide)] at gain
    omega
  have step (n : ℕ) (lo : 4 ≤ n) (hi : n < 8) :
      primitiveBack A b (n+1) =
        primitiveBack A b n ⊔ (primitiveBack A b n).map (diag (reflectedClock A)) := by
    refine primitiveBack_clock_step_of_unit_rank n ?_ (escape n lo hi)
    rw [ranks n lo (by omega),ranks (n+1) (by omega) (by omega)] <;> omega
  have one : finrank K (primitiveBack A b 4 ⊔
      (primitiveBack A b 4).map (diag (reflectedClock A)) : Submodule K (Fin s → K)) ≤
      finrank K (primitiveBack A b 4)+1 := by
    rw [←step 4 (by decide) (by decide),ranks 4 (by decide) (by decide),
      ranks 5 (by decide) (by decide)] <;> omega
  obtain ⟨r,U,w,positive,stable,inside,maximal,head,_,_,split⟩ :=
    single_head one (escape 4 (by decide) (by decide))
  have chains (k : ℕ) (hk : k ≤ 4) :
      primitiveBack A b (4+k) = chain (diag (reflectedClock A)) U w (r+k) := by
    induction k with
    | zero => simpa only [Nat.add_zero] using head
    | succ k ih =>
      have rp : 0 < r+k := by omega
      rw [show 4+(k+1)=(4+k)+1 by omega,step (4+k) (by omega) (by omega),
        ih (by omega),clock_chain_next (w:=w) stable rp] <;> rfl
  have finalHead : primitiveBack A b 8 =
      chain (diag (reflectedClock A)) U w (r+4) := chains 4 (by decide)
  have sites : r+4 < (HeadFiber.escapeSites (reflectedClock A) w U).card := by
    apply HeadFiber.more_escape_sites (n:=r+4) stable (by omega)
    rw [←finalHead]
    exact lastEscape
  have split5 : finrank K U + r = 5 :=
    split.symm.trans (ranks 4 (by decide) (by decide))
  have firstCore : 1 ≤ finrank K U := by
    let y := reflectedClock A
    let q := quadraticSeed A b
    have hcard : (weightedSites y q).card = 1 := oneClock
    obtain ⟨a,ha1⟩ := Finset.card_eq_one.mp hcard
    have alive : a ∈ weightedSites y q := by simp [ha1]
    obtain ⟨i,hi,_⟩ := mem_weightedSites.mp alive
    have nz : q ≠ 0 := fun e => hi (by simp [e])
    have scl : diag y q = a • q := by
      ext j
      by_cases hq : q j=0
      · simp only [diag_apply,Pi.smul_apply,smul_eq_mul,hq,mul_zero]
      · have hm : y j ∈ weightedSites y q := mem_weightedSites.mpr ⟨j,hq,rfl⟩
        rw [ha1,Finset.mem_singleton] at hm
        simp only [diag_apply,Pi.smul_apply,smul_eq_mul,hm]
    have invQ : (K ∙ q).map (diag y) ≤ K ∙ q := by
      rw [Submodule.map_span,Set.image_singleton,scl]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr
        ((K ∙ q).smul_mem _ (Submodule.mem_span_singleton_self _))
    have in1 : q ∈ primitiveBack A b 1 :=
      adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
    have mono : Monotone (primitiveBack A b) := monotone_nat_of_le_succ (adjointFlag_le_succ _)
    have qIn : (K ∙ q) ≤ primitiveBack A b 4 :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr (mono (by decide : 1≤4) in1)
    have lo := Submodule.finrank_mono (maximal _ invQ qIn)
    rwa [finrank_span_singleton nz] at lo
  have capCore : finrank K U ≤ 3 := by
    have mask : MaskInvariant (reflectedClock A) U :=
      clock_mask_invariant (fun _ hv => stable (Submodule.mem_map_of_mem hv))
    have mass (v : Fin s → K) (hv : v ∈ U) : ∑ i,v i=0 := by
      have h := mem_annih.mp (primitiveBack_annih ho 0 4 (by decide) (inside hv)) _
        (one_mem_treeSpace A 0)
      simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using h
    have enough := reverse_failed_clock_blocks ho U mask mass (r:=3) (by decide)
    have gain := ordered_hermite_outgoing Fin.revPerm (mat A.transpose) (causal_transpose ha)
      (reflectedClock A) b U (primitiveBack A b 5) mask
      (inside.trans (adjointFlag_le_succ _ _))
      (fun _ hv => adjointFlag_transpose _ _ (Submodule.mem_map_of_mem (inside hv)))
      3 enough (fun Q hQ => reverse_primitive_next 4 Q (by omega))
    rw [ranks 5 (by decide) (by decide)] at gain
    omega
  exact ⟨r,U,w,⟨last.reflected_zero ha first,tail,full,ranks,positive,stable,inside,
    maximal,split5,chains,firstCore,capCore,sites⟩⟩

end
end RKResearch.Certified.Graded.Reverse
