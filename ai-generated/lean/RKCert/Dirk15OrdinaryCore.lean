module

public import RKCert.Dirk15NonC2ReverseOrbit

@[expose] public section

/-! # True ordinary-core rank dispatch at the p15 minimal bands
A surviving maximal core of the larger rank is forced to be a hyperplane
in F5, with two consecutive unit gains. The weighted fifth-debut exclusion
of that chart is a separate theorem. -/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

def MaximalClockCore (A : Fin s → Fin s → K) (h : ℕ) (U : Submodule K (Vec K s)) : Prop :=
  U≤zeroSpace A h ∧ U.map (diag (nodes A))≤U ∧
    ∀ W : Submodule K (Vec K s), W≤zeroSpace A h → W.map (diag (nodes A))≤W → W≤U

/-- Relative rank cannot stall while a genuine column survives outside the
maximal invariant core. Using a sup avoids choosing a quotient basis. -/
theorem defect_rank_cap_of_maximal {h j : ℕ} {U : Submodule K (Vec K s)}
    (hU : MaximalClockCore A h U) (hj : j≤h) (out : ¬zeroSpace A j≤U) :
    finrank K (zeroSpace A j⊔U : Submodule K (Vec K s))+(h-j)≤finrank K (zeroSpace A h) := by
  let F := zeroSpace A
  let C' := diag (nodes A)
  have strict (k : ℕ) (hl : j≤k) (hu : k+1≤h) : F k⊔U < F (k+1)⊔U := by
    refine lt_of_le_of_ne (sup_le_sup_right (zeroSpace_mono A (Nat.le_succ k)) _) ?_
    intro eq
    have he : (F k⊔U).map C'≤F k⊔U := by
      apply Submodule.map_le_iff_le_comap.mpr
      apply sup_le
      · intro q hq
        apply Submodule.mem_comap.mpr
        rw [eq]
        exact (le_sup_left : F (k+1)≤F (k+1)⊔U) (diag_zeroSpace A k hq)
      · intro q hq
        exact (le_sup_right : U≤F k⊔U) (hU.2.1 (Submodule.mem_map_of_mem hq))
    have hs : F k⊔U≤F h := sup_le (zeroSpace_mono A (by omega)) hU.1
    exact out ((zeroSpace_mono A hl).trans (le_sup_left.trans (hU.2.2 _ hs he)))
  have bound (n : ℕ) (hn : j+n≤h) :
      finrank K (F j⊔U : Submodule K (Vec K s))+n≤finrank K (F (j+n)⊔U : Submodule K (Vec K s)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hprev := ih (by omega)
      have hg := Submodule.finrank_lt_finrank_of_lt (strict (j+n) (by omega) (by omega))
      rw [show j+(n+1)=j+n+1 by omega]
      omega
  have hB := bound (h-j) (by omega)
  rw [Nat.add_sub_of_le hj,sup_eq_left.mpr hU.1] at hB
  exact hB

variable [CharZero K]

/-- For the two charts with f7=f6+1, the largest invariant core is already
inside actual F6 and has rank at most 3+e. If it attains 3+e, then it
is a true invariant hyperplane of F5 and the two following gains are unit. -/
theorem order15_ordinary_core_rank {A : Fin 20 → Fin 20 → K} {b : Vec K 20}
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) {e : ℕ}
    (f3 : finrank K (zeroSpace A 3)=1+e)
    (f6 : finrank K (zeroSpace A 6)=5+e) (f7 : finrank K (zeroSpace A 7)=6+e)
    (U : Submodule K (Vec K 20)) (hU : MaximalClockCore A 7 U) :
    U≤zeroSpace A 6 ∧ finrank K U≤3+e ∧
      (finrank K U=3+e → U≤zeroSpace A 5 ∧ finrank K (zeroSpace A 5)=4+e) := by
  have inv (v : Vec K 20) (hv : v∈U) : diag (nodes A) v∈U :=
    hU.2.1 (Submodule.mem_map_of_mem hv)
  have plt (j : ℕ) (hj : 2≤j) (hp : j+1≤15) :
      finrank K (zeroSpace A j)<finrank K (zeroSpace A (j+1)) :=
    Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho hj hp)
  have f34 := plt 3 (by decide) (by decide)
  have f45 := plt 4 (by decide) (by decide)
  have f56 := plt 5 (by decide) (by decide)
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at f34
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at f45
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at f56
  have not7 : U≠zeroSpace A 7 := by
    intro he
    have bnd := dirk_forward_invariant_incoming ha ho (j:=7) (by decide) (he ▸ inv)
    change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 7) at bnd
    omega
  have rU7 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hU.1 not7)
  have out6 : ¬zeroSpace A 6≤U := by
    intro h6U
    have he : zeroSpace A 6=U := Submodule.eq_of_le_of_finrank_le h6U (by omega)
    have bb := dirk_forward_invariant_outgoing ha ho (j:=6) (by decide) U he.ge inv
    change finrank K U+3≤finrank K (zeroSpace A 7) at bb
    have rr := Submodule.finrank_mono h6U
    omega
  have b6 := defect_rank_cap_of_maximal hU (j:=6) (by decide) out6
  change finrank K (zeroSpace A 6⊔U : Submodule K (Vec K 20))+1≤finrank K (zeroSpace A 7) at b6
  have le6 : U≤zeroSpace A 6 := by
    have e6 : zeroSpace A 6=zeroSpace A 6⊔U :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    rw [e6]
    exact le_sup_right
  have rk := dirk_forward_invariant_outgoing ha ho (j:=6) (by decide) U le6 inv
  change finrank K U+3≤finrank K (zeroSpace A 7) at rk
  refine ⟨le6,by omega,fun cut => ?_⟩
  have f5max : finrank K (zeroSpace A 5)=4+e := by
    by_contra hne
    have f5min : finrank K (zeroSpace A 5)=3+e := by omega
    have h4U : zeroSpace A 4≤U := by
      by_contra not4
      have bc := defect_rank_cap_of_maximal hU (j:=4) (by decide) not4
      have hl : U < zeroSpace A 4⊔U := lt_of_le_of_ne le_sup_right
        (fun hEq => not4 (le_sup_left.trans hEq.ge))
      have lt' := Submodule.finrank_lt_finrank_of_lt hl
      change finrank K (zeroSpace A 4⊔U : Submodule K (Vec K 20))+3≤
        finrank K (zeroSpace A 7) at bc
      omega
    have out4 : ¬(zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := by
      intro inv4
      have r := dirk_forward_invariant_outgoing ha ho (j:=4) (by decide)
        (zeroSpace A 4) le_rfl (fun w hw => inv4 (Submodule.mem_map_of_mem hw))
      change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at r
      omega
    let Q := zeroSpace A 4⊔(zeroSpace A 4).map (diag (nodes A))
    have hb : zeroSpace A 4<Q := lt_of_le_of_ne le_sup_left
      (fun h => out4 (le_sup_right.trans h.ge))
    have hQU : Q≤U := sup_le h4U ((Submodule.map_mono h4U).trans hU.2.1)
    have hrank := Submodule.finrank_lt_finrank_of_lt hb
    have eQU : Q=U := Submodule.eq_of_le_of_finrank_le hQU (by omega)
    have le45 : Q≤zeroSpace A 5 := sup_le (zeroSpace_mono A (by decide))
      (fun z hz => by
        obtain ⟨v,hv,rfl⟩ := hz
        exact diag_zeroSpace A 4 hv)
    have le5 : U≤zeroSpace A 5 := eQU ▸ le45
    have e5 : U=zeroSpace A 5 := Submodule.eq_of_le_of_finrank_eq le5 (cut.trans f5min.symm)
    have bd := dirk_forward_invariant_incoming ha ho (j:=5) (by decide) (e5 ▸ inv)
    change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at bd
    omega
  have out5 : ¬zeroSpace A 5≤U := fun hle => by
    have hdim := Submodule.finrank_mono hle
    omega
  have b5 := defect_rank_cap_of_maximal hU (j:=5) (by decide) out5
  change finrank K (zeroSpace A 5⊔U : Submodule K (Vec K 20))+2≤finrank K (zeroSpace A 7) at b5
  have e5 : zeroSpace A 5=zeroSpace A 5⊔U :=
    Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  exact ⟨e5.symm ▸ le_sup_right,f5max⟩

end RKCert.Paired
