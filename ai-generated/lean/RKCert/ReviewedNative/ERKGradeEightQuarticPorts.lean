module

public import RKCert.ReviewedNative.NativeFlatClockHead
public import RKCert.ReviewedNative.ERKHeadContrast
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual two-pivot quartic obligations from the flat grade-four chart

This is native geometry over every characteristic-zero field: the head
and both clocks come from the original strictly triangular tableau.
No ordered-field or scalar elimination assumptions enter. -/
namespace RKResearch.Certified.Graded
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- The exact paid quartic obstruction in actual (unscaled) clock coordinates. -/
structure Quartic3Plus2 (P : K[X]) (u v : K) : Prop where
  nonzero : P≠0
  degree : P.natDegree≤4
  first_ne : u≠0
  second_ne : v≠0
  distinct : v≠u
  first : ∀ R : K[X], R.natDegree≤2 → (primitive (R*(X*P))).eval u=0
  second : ∀ R : K[X], R.natDegree≤1 → (primitive (R*(X*(X-C u)*P))).eval v=0

variable [CharZero K]

set_option maxRecDepth 3500 in
set_option maxHeartbeats 750000 in
theorem grade_four_flat_quartic_ports
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b) (pay : 16≤p)
    {r : ℕ} {U : Submodule K (Fin (s+1)→K)} {w : Fin (s+1)→K}
    (H : FlatClockHead A 4 4 r U w) :
    ∃ (P : K[X]) (i j : Fin (s+1)), Quartic3Plus2 P (nodes A i) (nodes A j) := by
  classical
  let c := nodes A
  let T := diag c
  have F4 : zeroSpace A 4=chain T U w r := by simpa only [Nat.add_zero] using H.flags 0 (by decide)
  have F8 : zeroSpace A 8=chain T U w (r+4) := H.flags 4 (by decide)
  have rp := H.positive
  have wp : w∈zeroSpace A 4 := by
    have paid := (clock_chain_le_iff r).mp F4.ge
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using paid.2 0 rp
  have keep {x y : Fin (s+1)→K} (hx : x∈U) (hy : y∈zeroSpace A 4) : x*y∈U :=
    HeadFiber.core_mul (A:=A) (j:=4) (k:=4) H.coreStable H.coreInside H.extraSites F8.le hx hy
  obtain ⟨v,disjoint,same⟩ := HeadFiber.disjoint_rep H.coreStable
    (fun x hx y hy => keep hx (H.coreInside hy)) (fun _ hx => keep hx wp)
  have Fb : zeroSpace A 4=chain T U v r := F4.trans (same r).symm
  have Fl : zeroSpace A 8=chain T U v (r+4) := F8.trans (same _).symm
  have escaped : ¬(zeroSpace A 8).map T≤zeroSpace A 8 := by
    intro inc
    have pre := ((clock_chain_le_iff (r+4)).mp F8.ge).2 (r+4-1) (by omega)
    have h : T ((T^(r+4-1)) w)∈zeroSpace A 8 := inc (Submodule.mem_map_of_mem pre)
    have identity : T^ (r+4) = T * (T^(r+4-1)) := by
      rw [←pow_succ',show r+4-1+1=r+4 by omega]
    apply H.unpaid
    change (T^(r+4)) w ∈zeroSpace A 8
    rw [identity,Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact h
  have many : r+4 < (HeadFiber.physicalSites c v).card := by
    apply (HeadFiber.more_escape_sites H.coreStable (show 0<r+4 by omega) ?_).trans_le
      (Finset.card_le_card HeadFiber.escape_le_physical)
    rwa [←Fl]
  have paid := (clock_chain_le_iff r).mp Fb.ge
  have v4 : v∈zeroSpace A 4 := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using paid.2 0 rp
  have sq (k : ℕ) (hk : k≤(r-1)+(r-1)) : (T^k) (v*v)∈chain T U v (r+4) := by
    let a := min k (r-1)
    let d := k-a
    have ar : a<r := by dsimp [a]; omega
    have dr : d<r := by dsimp [a,d]; omega
    have ad : a+d=k := by dsimp [a,d]; omega
    have e : (T^k) (v*v) = ((T^a) v)*((T^d) v) := by
      ext t
      simp only [T,HeadFiber.clock_power_value,Pi.mul_apply]
      rw [←ad,pow_add]
      ring
    rw [e,←Fl]
    exact zeroSpace_mul (A:=A) (m:=4) (n:=4) (paid.2 a ar) (paid.2 d dr)
  obtain ⟨P,bound,on⟩ := HeadFiber.multiplier_polynomial (a:=v) (w:=v) (c:=c) (U:=U)
    disjoint many sq
  have pn : P≠0 := by
    intro z
    have vz : v=0 := by
      ext i
      by_contra h
      exact h ((on i h).trans (by simp [z]))
    rw [vz] at many
    simp [HeadFiber.physicalSites] at many
  have pd : P.natDegree≤4 := by have h := bound.resolve_left pn; omega
  have poff (x : Fin (s+1)→K) (hx : x∈U) (i : Fin (s+1)) (hi : v i≠0) : x i=0 := by
    by_contra hn
    exact hi (disjoint i ⟨x,hx,hn⟩)
  have ps : PolySeparated A 8 := PolySeparated.of_coeff (explicit_coeff_separated ha ho pay)
  have test := HeadContrast.head_contrast_at_physical_row ha ho (j:=4) (H:=8)
    (by omega) ps U H.coreInside (fun _ hx=>H.coreStable (Submodule.mem_map_of_mem hx))
    v v4 Fl.le poff P pn pd on
  obtain ⟨i,ip,first⟩ := test X X_ne_zero (by rw [natDegree_X]; decide)
  let u := c i
  have un : u≠0 := fun z => ip (by simp [eval_mul,show nodes A i=0 from z])
  let Q : K[X] := X*(X-C u)
  have qn : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  have qd : Q.natDegree=2 := by
    dsimp only [Q]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨j,jp,second⟩ := test Q qn (by rw [qd]; decide)
  let t := c j
  have tn : t≠0 := fun z => jp (by simp [Q,eval_mul,show nodes A j=0 from z])
  have tu : t≠u := fun z => jp (by simp [Q,eval_mul,show nodes A j=u from z])
  refine ⟨P,i,j,⟨pn,pd,un,tn,tu,?_,?_⟩⟩
  · intro R d
    exact first R (by rw [natDegree_X]; omega)
  · intro R d
    exact second R (by rw [qd]; omega)

end RKResearch.Certified.Graded
