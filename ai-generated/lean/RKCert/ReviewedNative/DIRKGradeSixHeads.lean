module

public import RKCert.ReviewedNative.ClockHeadSupport
public import RKCert.ReviewedNative.DIRKGradeSixBand

@[expose] public section

/-! # The two physical heads of a failed ordinary grade-six surplus
Both profiles are deduced from the original lower-triangular tableau,
the reviewed `HasOrder`, the three unit rank costs, and native graded
products. The current theorem is a reduction, not either profile's
chronological exclusion. -/
namespace RKResearch.Certified.Graded

open Polynomial RKCert.OneEscape Module
open scoped Matrix Classical
variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K}
variable {b : Fin s → K}

private theorem grow_head {j h r : ℕ} {U : Submodule K (Fin s → K)} {w : Fin s → K}
    (stable : U.map (diag (nodes A)) ≤ U) (pos : 0<r)
    (base : zeroSpace A j = chain (diag (nodes A)) U w r)
    (unit : ∀ k<h, finrank K (zeroSpace A (j+k+1)) ≤ finrank K (zeroSpace A (j+k))+1)
    (out : ∀ k<h, ¬(zeroSpace A (j+k)).map (diag (nodes A)) ≤ zeroSpace A (j+k)) :
    ∀ k≤h, zeroSpace A (j+k) = chain (diag (nodes A)) U w (r+k) := by
  intro k hk
  induction k with
  | zero => simpa using base
  | succ k ih =>
    rw [show j+(k+1)=j+k+1 by omega,zeroSpace_clock_step_of_unit (unit k (by omega)) (out k (by omega)),
      ih (by omega)]
    exact clock_chain_next stable (by omega)

variable [CharZero K]

/-- When F3 is clock-invariant the core of the grade-four head is F3
itself. It is closed under pointwise multiplication and the single head
escapes on at least four genuinely different clock blocks modulo F3. -/
theorem dirk_grade_six_head_at_four (ha : A.IsLowerTriangular) (ho : HasOrder A b p) (pay : 7≤p)
    (bad : ¬finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6))
    (inv : (zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3) :
    ∃ w : Fin s → K,
      (∀ u∈zeroSpace A 3, ∀ v∈zeroSpace A 3, u*v∈zeroSpace A 3) ∧
      3 < (HeadFiber.escapeSites (nodes A) w (zeroSpace A 3)).card ∧
      (∀ k≤2, zeroSpace A (4+k)=chain (diag (nodes A)) (zeroSpace A 3) w (1+k)) := by
  obtain ⟨step,out⟩ := dirk_unit_band_of_no_grade_six_surplus ha ho pay bad
  have e4 := zeroSpace_clock_step_of_unit (step 4 (by decide) (by decide)).le (out 4 (by decide) (by decide))
  obtain ⟨r,U,w,pos,stable,_,big,base,_,_,dim⟩ :=
    single_head (T:=diag (nodes A)) (F:=zeroSpace A 4) (by rw [←e4]; exact (step 4 (by decide) (by decide)).le)
      (out 4 (by decide) (by decide))
  have inside := big _ inv (zeroSpace_mono A (by decide : 3≤4))
  have du := Submodule.finrank_mono inside
  have cost : finrank K (zeroSpace A 4)=finrank K (zeroSpace A 3)+1 := step 3 (by decide) (by decide)
  have r1 : r=1 := by omega
  have eq : zeroSpace A 3=U := Submodule.eq_of_le_of_finrank_eq inside (by omega)
  subst r
  subst U
  have band := grow_head (h:=2) stable (by decide) base
    (fun k hk => (step (4+k) (by omega) (by omega)).le) (fun k hk => out (4+k) (by omega) (by omega))
  have b6 : zeroSpace A 6=chain (diag (nodes A)) (zeroSpace A 3) w 3 := band 2 (by decide)
  have esc := out 6 (by decide) (by decide)
  rw [b6] at esc
  have sites := HeadFiber.more_escape_sites stable (by decide) esc
  exact ⟨w,fun _ hu _ hv => HeadFiber.core_mul (j:=3) (k:=3) stable le_rfl sites b6.le hu hv, sites,band⟩

/-- In the other branch a single physical head is present already at F3.
It can be chosen off all live core coordinates and is polynomial on its
own support. Its degree plus the initial clock-chain length is at most
four, and there are more than r+3 actually distinct head clocks. -/
theorem dirk_grade_six_head_at_three (ha : A.IsLowerTriangular) (ho : HasOrder A b p) (pay : 7≤p)
    (bad : ¬finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6))
    (esc3 : ¬(zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3) :
    ∃ (r : ℕ) (U : Submodule K (Fin s → K)) (w : Fin s → K) (P : K[X]),
      0<r ∧ U.map (diag (nodes A))≤U ∧ U≤zeroSpace A 3 ∧
      (∀ u∈U, ∀ v∈U, u*v∈U) ∧ (∀ i, (∃ u∈U, u i≠0) → w i=0) ∧
      r+3 < (HeadFiber.physicalSites (nodes A) w).card ∧
      (∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) U w (r+k)) ∧
      P≠0 ∧ P.natDegree+r≤4 ∧ (∀ i, w i≠0 → w i=P.eval (nodes A i)) := by
  classical
  obtain ⟨step,out⟩ := dirk_unit_band_of_no_grade_six_surplus ha ho pay bad
  have e3 := zeroSpace_clock_step_of_unit (step 3 (by decide) (by decide)).le esc3
  obtain ⟨r,U,w,pos,stable,inside,_,base,paid,_,_⟩ :=
    single_head (T:=diag (nodes A)) (F:=zeroSpace A 3) (by rw [←e3]; exact (step 3 (by decide) (by decide)).le) esc3
  have band := grow_head (h:=3) stable pos base
    (fun k hk => (step (3+k) (by omega) (by omega)).le) (fun k hk => by
      by_cases k0 : k=0
      · simpa [k0] using esc3
      · exact out (3+k) (by omega) (by omega))
  have b6 : zeroSpace A 6=chain (diag (nodes A)) U w (r+3) := band 3 (by decide)
  have esc6 := out 6 (by decide) (by decide)
  have esc := esc6
  rw [b6] at esc
  have sites := HeadFiber.more_escape_sites stable (by omega) esc
  have keep (u) (hu : u∈U) (v) (hv : v∈zeroSpace A 3) : u*v∈U :=
    HeadFiber.core_mul (j:=3) (k:=3) stable inside sites b6.le hu hv
  have closed (u) (hu : u∈U) (v) (hv : v∈U) : u*v∈U := keep u hu v (inside hv)
  have hw : w∈zeroSpace A 3 := by simpa using paid 0 pos
  obtain ⟨v,disjoint,shift⟩ := HeadFiber.disjoint_rep stable closed (fun u hu => keep u hu w hw)
  have chart (k : ℕ) (hk : k≤3) : zeroSpace A (3+k)=chain (diag (nodes A)) U v (r+k) :=
    (band k hk).trans (shift _).symm
  have eq6 : zeroSpace A 6=chain (diag (nodes A)) U v (r+3) := chart 3 (by decide)
  rw [eq6] at esc6
  have many := (HeadFiber.more_escape_sites stable (by omega) esc6).trans_le
    (Finset.card_le_card HeadFiber.escape_le_physical)
  have square (k : ℕ) (hk : k≤2*r-2) :
      (diag (nodes A)^k) (v*v) ∈ chain (diag (nodes A)) U v (r+3) := by
    let i := min k (r-1)
    let l := k-i
    have il : i+l=k := Nat.add_sub_of_le (Nat.min_le_left _ _)
    have i0 : i<r := (Nat.min_le_right _ _).trans_lt (by omega)
    have l0 : l<r := by dsimp [l,i]; omega
    have eq3 : zeroSpace A 3 = chain (diag (nodes A)) U v r := by simpa using chart 0 (by decide)
    have power (t : ℕ) (ht : t<r) : (diag (nodes A)^t) v∈zeroSpace A 3 :=
      ((clock_chain_le_iff r).mp eq3.ge).2 t ht
    have prod := zeroSpace_mul (power i i0) (power l l0)
    rw [←eq6]
    convert prod using 1
    ext x
    simp only [HeadFiber.clock_power_value,Pi.mul_apply]
    rw [←il,pow_add]
    ring
  obtain ⟨P,degree,values⟩ := HeadFiber.multiplier_polynomial disjoint many square
  have nz : P≠0 := by
    intro pz
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0<(HeadFiber.physicalSites (nodes A) v).card by omega)
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hn := (Finset.mem_filter.mp hi).2
    exact hn (by simpa [pz] using values i hn)
  have d := degree.resolve_left nz
  exact ⟨r,U,v,P,pos,stable,inside,closed,disjoint,many,chart,nz,by omega,values⟩

end RKResearch.Certified.Graded
