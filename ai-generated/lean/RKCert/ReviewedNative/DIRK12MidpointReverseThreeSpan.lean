module

public import RKCert.ReviewedNative.DIRK12MidpointForwardActualLow
public import RKCert.ReviewedNative.DIRK12MidpointPolynomialVector
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual ten physical nonterminal ordinary coordinates give
exactly three reverse annihilator directions through degree six.
The proof is constructive: split the repeated physical pair, fit the
two genuine barycentric modes at two distinct labels, and use the
seven remaining Lagrange cardinals. No matrix rank oracle is used. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded Polynomial
open DIRK12MidpointForward DIRK12MidpointForward.Late
open DIRK12MidpointRealInterval DirectedRatBox DIRK12MidpointProbes
open scoped Matrix BigOperators Polynomial

section
variable (x f : ℝ)
local notation "Areal" => (Feed.tableau (assembled x f))
local notation "Cphys" => (nodes Areal)
local notation "Yphys" => ((1:V15 ℝ)-Cphys)
local notation "G" => (profileG x f)
local notation "H" => (profileH x f)

theorem representative_cover (i : Fin 15) :
    i=13 ∨ i=terminal ∨ ghostRow i ∨ ∃ j : Fin 9, i=representative j := by
  fin_cases i <;> decide

private theorem stage_d1 {i : Fin 15} (hg : ghostRow i) : i≠13 := by
  intro e
  subst i
  exact (by decide : ¬ghostRow (13:Fin 15)) hg

private theorem stage_d2 {i : Fin 15} (hg : ghostRow i) : i≠11 := by
  intro e
  subst i
  exact (by decide : ¬ghostRow (11:Fin 15)) hg

theorem G_zero_ghost (i : Fin 15) (hg : ghostRow i) : G i=0 := by
  simp only [profileG,Physical.G,physicalPair,ite_eq_right (stage_d1 hg),
    ite_eq_right (stage_d2 hg)]

theorem G_zero_terminal : G terminal=0 := by
  simp only [profileG,Physical.G,physicalPair,ite_eq_right (by decide : terminal≠(13:Fin 15)),
    ite_eq_right (by decide : terminal≠(11:Fin 15))]

theorem G_at_13 : G 13=Physical.paired (zeroHead x f) (exactData x f) := by
  simp [profileG,Physical.G,physicalPair]

theorem reflected_rep (j : Fin 9) : Yphys (representative j)=liveNode x f j := by
  change 1-Cphys (representative j)=site x f j.succ
  rw [←represented_tag]
  exact assembled_real_nodes x f _ (representative_nonghost j)

theorem Y_times_G : Yphys*G=d x f • G := by
  have c13 := assembled_real_nodes x f (13:Fin 15) (by decide)
  have c11 := assembled_real_nodes x f (11:Fin 15) (by decide)
  change Yphys 13=d x f at c13
  change Yphys 11=d x f at c11
  funext i
  change Yphys i*G i=d x f*G i
  by_cases e : i=13
  · subst i
    rw [c13]
  · by_cases b : i=11
    · subst i
      rw [c11]
    · simp [profileG,Physical.G,physicalPair,e,b]

section Roots
variable (hx : Encloses xBox x) (hf : Encloses fBox f)
include hx hf

theorem H_zero_ghost (i : Fin 15) (hg : ghostRow i) : H i=0 := by
  rw [actual_H_eq x f hx hf]
  apply bary_absent
  intro j e
  exact representative_nonghost j (e.symm ▸ hg)

theorem H_zero_terminal : H terminal=0 := by
  rw [actual_H_eq x f hx hf,bary_terminal]

theorem H_zero_13 : H 13=0 := by rw [actual_H_eq x f hx hf,bary_13]

theorem YH_silent (m : Nat) (hm : m≤6) : row (Yphys*H) (Cphys^m)=0 := by
  rw [Vector.clock_slide]
  have e : Yphys*Cphys^m=Cphys^m-Cphys^(m+1) := by
    funext i
    simp only [Pi.mul_apply,Pi.sub_apply,Pi.one_apply,Pi.pow_apply,pow_succ]
    ring
  rw [e,map_sub,actual_H_silent x f hx hf m (by omega),
    actual_H_silent x f hx hf (m+1) (by omega),sub_self]

theorem rho_nz : rho x f≠0 := by
  have q : cofactor2 x f (d x f) (u x f)/v x f≠0 := by
    intro r0
    have v := mass_v x f
    rw [r0,mul_zero] at v
    exact cardinalWeight_nonzero hx hf 8 v
  have rg := ratio_guards hx hf
  have p : Seed.p (r x f)≠0 := by
    apply div_ne_zero (pow_ne_zero _ rg.1)
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr rg.2.1)
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (d_pos hx hf).ne')
    (mul_ne_zero Seed.sigma_nz p)) q

theorem H_rep_nz (j : Fin 9) : H (representative j)≠0 := by
  rw [actual_H_eq x f hx hf,bary_at_rep]
  exact mul_ne_zero (rho_nz x f hx hf) (liveWeight_nz hx hf j)

private def seven : Finset (Fin 9) := (Finset.univ.erase 0).erase 1

omit hx hf in
private theorem seven_card : seven.card=7 := by decide +kernel

omit hx hf in
private theorem seven_mem (j : Fin 9) : j∈seven ↔ j≠0 ∧ j≠1 := by
  simp [seven,and_comm]

/-- Seven literal coordinate probes separate a residual after the
first two labels and the other physical pair entry are removed. -/
theorem seven_site_zero (z : V15 ℝ)
    (zg : ∀ i, ghostRow i → z i=0) (zt : z terminal=0) (zd : z 13=0)
    (z0 : z (representative 0)=0) (z1 : z (representative 1)=0)
    (silent : ∀ m≤6, row z (Cphys^m)=0) : z=0 := by
  have kill (j : Fin 9) : z (representative j)=0 := by
    by_cases e0 : j=0
    · exact e0.symm ▸ z0
    by_cases e1 : j=1
    · exact e1.symm ▸ z1
    have jmem : j∈seven := (seven_mem j).2 ⟨e0,e1⟩
    let p := Lagrange.basis seven (liveNode x f) j
    have inj : Set.InjOn (liveNode x f) (↑seven : Set (Fin 9)) :=
      Set.injOn_of_injective (liveNode_distinct hx hf)
    have dp : p.natDegree≤6 := by
      have q := Lagrange.natDegree_basis inj jmem
      change p.natDegree=seven.card-1 at q
      rw [q,seven_card]
    have q := Vector.silent_reflected Cphys z p 6 dp silent
    rw [row_apply,dotProduct] at q
    have sum0 :
        (∑ i : Fin 15, z i*Vector.evalVector Yphys p i)=
          z (representative j)*Vector.evalVector Yphys p (representative j) := by
      apply Finset.sum_eq_single_of_mem _ (Finset.mem_univ _)
      intro i _ ne
      rcases representative_cover i with a|a|a|⟨k,a⟩
      · rw [a,zd,zero_mul]
      · rw [a,zt,zero_mul]
      · rw [zg i a,zero_mul]
      · rw [a]
        by_cases k0 : k=0
        · rw [k0,z0,zero_mul]
        by_cases k1 : k=1
        · rw [k1,z1,zero_mul]
        have km : k∈seven := (seven_mem k).2 ⟨k0,k1⟩
        have n : j≠k := by intro e; exact ne (a.trans (congrArg representative e.symm))
        have P0 := Lagrange.eval_basis_of_ne (v:=liveNode x f) n km
        change (p.eval (liveNode x f k))=0 at P0
        rw [Vector.at_apply,reflected_rep x f k,P0,mul_zero]
    have P1 := Lagrange.eval_basis_self inj jmem
    change p.eval (liveNode x f j)=1 at P1
    rw [sum0,Vector.at_apply,reflected_rep x f j,P1,mul_one] at q
    exact q
  funext i
  rcases representative_cover i with h|h|h|⟨j,h⟩
  · exact h.symm ▸ zd
  · exact h.symm ▸ zt
  · exact zg i h
  · exact h.symm ▸ kill j

/-- The full actual three-direction characterization at paid degree
six. Two nonzero barycentric entries determine the fit, regardless
of the signs of the individual or aggregate ordinary masses. -/
theorem annihilator_three (z : V15 ℝ)
    (zg : ∀ i, ghostRow i → z i=0) (zt : z terminal=0)
    (silent : ∀ m≤6, row z (Cphys^m)=0) :
    ∃ a b c : ℝ, z=a • G+b • H+c • (Yphys*H) := by
  let s := Physical.paired (zeroHead x f) (exactData x f)
  have sn : s≠0 := Physical.paired_nz _ _ (assembled_geom x f hx hf)
  let a := z 13/s
  let w := z-a • G
  let i0 := representative 0
  let i1 := representative 1
  let p0 := w i0/(H i0)
  let p1 := w i1/(H i1)
  let y0 := Yphys i0
  let y1 := Yphys i1
  have yne : y1-y0≠0 := by
    change Yphys (representative 1)-Yphys (representative 0)≠0
    rw [reflected_rep x f 1,reflected_rep x f 0]
    exact sub_ne_zero.mpr (fun e => (by decide : (1:Fin 9)≠0) (liveNode_distinct hx hf e))
  let c := (p1-p0)/(y1-y0)
  let b := p0-c*y0
  let q := w-b • H-c • (Yphys*H)
  have s0 : b+c*y0=p0 := by dsimp only [b]; ring
  have s1 : b+c*y1=p1 := by
    have j := div_mul_cancel₀ (p1-p0) yne
    change c*(y1-y0)=p1-p0 at j
    dsimp only [b]
    linear_combination j
  have q0 : q i0=0 := by
    change w i0-b*H i0-c*(y0*H i0)=0
    rw [show w i0-b*H i0-c*(y0*H i0)=w i0-(b+c*y0)*H i0 by ring,
      s0,div_mul_cancel₀ _ (H_rep_nz x f hx hf 0),sub_self]
  have q1 : q i1=0 := by
    change w i1-b*H i1-c*(y1*H i1)=0
    rw [show w i1-b*H i1-c*(y1*H i1)=w i1-(b+c*y1)*H i1 by ring,
      s1,div_mul_cancel₀ _ (H_rep_nz x f hx hf 1),sub_self]
  have w13 : w 13=0 := by
    change z 13-a*G 13=0
    rw [G_at_13]
    change z 13-(z 13/s)*s=0
    rw [div_mul_cancel₀ _ sn,sub_self]
  have q13 : q 13=0 := by
    change w 13-b*H 13-c*(Yphys 13*H 13)=0
    rw [w13,H_zero_13 x f hx hf]
    ring
  have gh (i : Fin 15) (hg : ghostRow i) : q i=0 := by
    change z i-a*G i-b*H i-c*(Yphys i*H i)=0
    rw [zg i hg,G_zero_ghost x f i hg,H_zero_ghost x f hx hf i hg]
    ring
  have nt : q terminal=0 := by
    change z terminal-a*G terminal-b*H terminal-c*(Yphys terminal*H terminal)=0
    rw [zt,G_zero_terminal x f,H_zero_terminal x f hx hf]
    ring
  have qt (m : Nat) (hm : m≤6) : row q (Cphys^m)=0 := by
    dsimp only [q,w]
    rw [Vector.left_sub,Vector.left_sub,Vector.left_sub,
      Vector.left_smul,Vector.left_smul,Vector.left_smul,
      silent m hm,actual_G_silent x f hx hf m,
      actual_H_silent x f hx hf m (by omega),YH_silent x f hx hf m hm]
    ring
  have done := seven_site_zero x f hx hf q gh nt q13 q0 q1 qt
  refine ⟨a,b,c,?_⟩
  funext i
  have j := congrFun done i
  change z i-a*G i-b*H i-c*(Yphys i*H i)=0 at j
  change z i=a*G i+b*H i+c*(Yphys i*H i)
  linear_combination j

end Roots
end
end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.rho_nz
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.YH_silent
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.seven_site_zero
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.annihilator_three
