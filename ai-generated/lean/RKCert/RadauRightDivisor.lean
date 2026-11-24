module

public import RKCert.RadauGridComplete
public import RKCert.RadauRightMoment
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! # Right-Radau omitted moment for an arbitrary monic divisor
Factoring is done only in algebraic closure, and faithful change of
coefficient field preserves the genuinely paid characteristic-zero moment. -/
namespace RKCert.FixedPolynomial.Radau77569
open Polynomial RKCert.Paired RKCert.Paired.Signature RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def rightRadau7 : K[X] := reflectPolynomial radauLeft7

omit [CharZero K] in
@[simp] theorem eval_rightRadau7 (u : K) :
    (rightRadau7 : K[X]).eval u=(radauLeft7 : K[X]).eval (1-u) := by
  simp [rightRadau7,reflectPolynomial,Polynomial.eval_comp]

theorem rightRadau7_ne : (rightRadau7 : K[X])≠0 := by
  intro e
  apply radau_left_zero_ne (K:=K)
  simpa only [eval_rightRadau7,sub_self,eval_zero] using congrArg (Polynomial.eval (1:K)) e

omit [CharZero K] in
theorem rightRadau7_degree_le : (rightRadau7 : K[X]).natDegree≤7 :=
  (reflectPolynomial_degree _).trans radauLeft7_degree_le

theorem rightRadau7_nodup [IsAlgClosed K] : (rightRadau7 : K[X]).roots.Nodup := by
  classical
  obtain ⟨S,sc,hs⟩ := exists_eight_ports (K:=K)
  let T := (S.erase 0).image (fun x : K => 1-x)
  have inj : Function.Injective (fun x : K => 1-x) := by
    intro x y e
    linear_combination -e
  have tc : 7≤T.card := by
    change 7≤((S.erase 0).image _).card
    rw [Finset.card_image_of_injective _ inj]
    by_cases h0 : 0∈S
    · rw [Finset.card_erase_of_mem h0,sc]
    · rw [Finset.erase_eq_of_notMem h0,sc]
      decide
  let R : K[X] := rightRadau7
  have inc : T⊆R.roots.toFinset := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨han,has⟩ := Finset.mem_erase.mp ha
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots rightRadau7_ne).mpr
    change (rightRadau7 : K[X]).eval (1-a)=0
    rw [eval_rightRadau7,show 1-(1-a)=a by ring]
    exact (hs a has).resolve_left han
  have h₀ := tc.trans (Finset.card_le_card inc)
  have h₁ := Multiset.toFinset_card_le R.roots
  have h₂ := (card_roots' R).trans rightRadau7_degree_le
  change R.roots.Nodup
  exact (Multiset.toFinset_card_eq_card_iff_nodup).mp (by omega)

theorem right_divisor_paid_ne_of_split [IsAlgClosed K] {T : K[X]} (hm : T.Monic)
    (dT : T.natDegree≤4) (div : T∣(rightRadau7 : K[X])) {u : K}
    (ur : (rightRadau7 : K[X]).eval u=0) (uo : T.eval u≠0) :
    paidMoment T u 1≠0 := by
  classical
  have root_le := roots.le_of_dvd rightRadau7_ne div
  have nd := Multiset.nodup_of_le root_le rightRadau7_nodup
  have split := IsAlgClosed.splits T
  let S := T.roots.toFinset
  have cS : S.card=T.natDegree := (Multiset.toFinset_card_of_nodup nd).trans
    split.natDegree_eq_card_roots.symm
  let e := (Finset.equivFinOfCardEq cS).symm
  let a : Fin T.natDegree → K := fun i => (e i).val
  have inj : Function.Injective a := fun _ _ h => e.injective (Subtype.ext h)
  have sur (i : Fin T.natDegree) : a i∈T.roots :=
    Multiset.mem_toFinset.mp (e i).prop
  have apart (i : Fin T.natDegree) : a i≠u := by
    intro he
    exact uo ((mem_roots hm.ne_zero).mp (he ▸ sur i))
  have rt (i : Fin T.natDegree) : (radauLeft7 : K[X]).eval (1-a i)=0 := by
    have h := (mem_roots rightRadau7_ne).mp (Multiset.mem_of_le root_le (sur i))
    change (rightRadau7 : K[X]).eval (a i)=0 at h
    rwa [eval_rightRadau7] at h
  have factor : T=∏ i : Fin T.natDegree, (X - C (a i)) := by
    calc
      T = (T.roots.map (fun x => X-C x)).prod := split.eq_prod_roots_of_monic hm
      _ = ∏ x∈S,(X-C x) := by
        change _ = (S.val.map _).prod
        rw [show S.val=T.roots from Multiset.dedup_eq_self.mpr nd]
      _ = ∏ x : S, (X - C (x:K)) :=
        Finset.prod_subtype S (fun _ => Iff.rfl) (fun x => X-C x)
      _ = ∏ i : Fin T.natDegree, (X - C (a i)) :=
        (e.prod_comp (fun x : S => X - C (x:K))).symm
  rw [factor]
  exact right_omitted_primitive_ne dT u a inj apart ((eval_rightRadau7 u).symm.trans ur) rt

section Base
variable {L : Type*} [Field L] [CharZero L] (φ : K→+*L)

theorem map_paidMoment (T : K[X]) (u : K) (j : ℕ) :
    φ (paidMoment T u j)=paidMoment (T.map φ) (φ u) j := by
  unfold paidMoment
  rw [primitive_eval_power_mul T u j (d:=T.natDegree) le_rfl,
    primitive_eval_power_mul (T.map φ) (φ u) j (d:=T.natDegree) natDegree_map_le]
  simp only [map_sum,map_div₀,map_mul,map_pow,map_natCast,coeff_map]

omit [CharZero K] [CharZero L] in
theorem map_radauRight : (rightRadau7 : K[X]).map φ=(rightRadau7 : L[X]) := by
  have hL : (radauLeft7 : K[X]).map φ=(radauLeft7 : L[X]) := by
    rw [←map_reproducer (K:=K),←map_reproducer (K:=L),Polynomial.map_map]
    congr 1
    ext x
    simp
  simp only [rightRadau7,reflectPolynomial,Polynomial.map_comp,hL,Polynomial.map_sub,
    Polynomial.map_one,Polynomial.map_X]

end Base

theorem right_divisor_paid_ne {T : K[X]} (hm : T.Monic)
    (dT : T.natDegree≤4) (div : T∣(rightRadau7 : K[X])) {u : K}
    (ur : (rightRadau7 : K[X]).eval u=0) (uo : T.eval u≠0) :
    paidMoment T u 1≠0 := by
  let f := algebraMap K (AlgebraicClosure K)
  have h : T.map f∣(rightRadau7 : (AlgebraicClosure K)[X]) := by
    rw [←map_radauRight f]
    exact map_dvd (Polynomial.mapRingHom f) div
  have hu : (rightRadau7 : (AlgebraicClosure K)[X]).eval (f u)=0 := by
    rw [←map_radauRight f,eval_map_apply,ur,map_zero]
  have hn : (T.map f).eval (f u)≠0 := by
    rw [eval_map_apply]
    exact fun z => uo (f.injective (z.trans f.map_zero.symm))
  intro zero
  apply right_divisor_paid_ne_of_split (hm.map f) (natDegree_map_le.trans dT) h hu hn
  rw [←map_paidMoment f,zero,map_zero]

end
end RKCert.FixedPolynomial.Radau77569
