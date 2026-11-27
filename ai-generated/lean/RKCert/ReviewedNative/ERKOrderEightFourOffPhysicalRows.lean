module

public import RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalRepeat

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal late clean rows of the native ERK8 four-off branch

Only the two paid reverse rows J₁ and J₂ occur. Nothing here excludes
the branch or constructs a clean-grid scalar contradiction.
-/
namespace RKResearch.Certified.Graded.FourOffPhysical

open RKResearch Module Polynomial Reverse OneOff ERKTaggedHorizon ERK8PaidField
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]} {i : Fin 10}

private abbrev y (A : Matrix (Fin 10) (Fin 10) K) := reflectedClock A
private abbrev J (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K) := reflectedStageRow A b
private noncomputable abbrev Δ (A : Matrix (Fin 10) (Fin 10) K) (i : Fin 10) :=
  mat A.transpose (contrast K i 8)

private theorem tag_match_early (R : RepeatAtEight A b i) {k : Fin 10} (kk : k<8)
    (l : Fin 10) : SameTag A l k ↔ l=k ∨ (l=8 ∧ k=i) := by
  constructor
  · intro eq
    by_cases lk : l=k
    · exact Or.inl lk
    rcases lt_or_gt_of_ne lk with lt|lt
    · exact ((ne_of_lt kk) (R.unique lt eq).2).elim
    · exact Or.inr ⟨(R.unique lt eq.symm).2,(R.unique lt eq.symm).1⟩
  · rintro (rfl|⟨rfl,rfl⟩)
    · exact ⟨rfl,Iff.rfl⟩
    · exact R.same.symm

private theorem sum_early_tag (w : Fin 10 → K) {k : Fin 10} (kk : k<8) :
    (∑ l : Fin 10, if l=k ∨ (l=8 ∧ k=i) then w l else 0) =
      w k + (if k=i then w 8 else 0) := by
  classical
  by_cases eq : k=i
  · subst k
    simp only [and_true,if_pos rfl]
    let f : Fin 10 → K := fun l => if l=i ∨ l=8 then w l else 0
    change (∑ l : Fin 10, f l)=w i+w 8
    have e : (∑ l ∈ ({i,8}:Finset (Fin 10)), f l) = ∑ l : Fin 10, f l := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ no
      simp only [Finset.mem_insert,Finset.mem_singleton] at no
      exact if_neg no
    rw [←e,Finset.sum_pair (ne_of_lt kk)]
    simp [f]
  · simp [eq]

theorem offMass_at_early (R : RepeatAtEight A b i) (w : Fin 10 → K)
    {k : Fin 10} (kk : k<8) (gk : g A k≠0) :
    offMass A w (nodes A k)=w k+(if k=i then w 8 else 0) := by
  have e (l : Fin 10) :
      (g A l≠0 ∧ nodes A l=nodes A k) ↔ SameTag A l k := by
    constructor
    · rintro ⟨gl,cc⟩
      exact ⟨cc,iff_of_false gl gk⟩
    · intro T
      exact ⟨fun gl => gk (T.2.mp gl),T.1⟩
  simp_rw [offMass,e,tag_match_early R kk]
  exact sum_early_tag w kk

theorem cleanMass_at_early (R : RepeatAtEight A b i) (w : Fin 10 → K)
    {k : Fin 10} (kk : k<8) (gk : g A k=0) :
    cleanMass A w (nodes A k)=w k+(if k=i then w 8 else 0) := by
  have e (l : Fin 10) :
      (g A l=0 ∧ nodes A l=nodes A k) ↔ SameTag A l k := by
    constructor
    · rintro ⟨gl,cc⟩
      exact ⟨cc,iff_of_true gl gk⟩
    · intro T
      exact ⟨T.2.mpr gk,T.1⟩
  simp_rw [cleanMass,e,tag_match_early R kk]
  exact sum_early_tag w kk

private theorem delta8_zero (ha : ∀ i j, i≤j → A i j=0) (R : RepeatAtEight A b i) :
    Δ A i 8=0 := by
  change mat A.transpose (contrast K i 8) (8:Fin 10)=0
  rw [transpose_contrast_apply,ha 8 8 le_rfl,ha i 8 R.before.le,sub_zero]

private theorem delta_early_off_nonzero (ha : ∀ i j, i≤j → A i j=0)
    (R : RepeatAtEight A b i) {k : Fin 10} (kk : k<8) (gk : g A k≠0) :
    Δ A i k≠0 := by
  have ne := R.transposeResidues (nodes A k) (mem_offKnots.mpr ⟨k,gk,rfl⟩)
  change offMass A (Δ A i) (nodes A k)≠0 at ne
  rw [offMass_at_early R (Δ A i) kk gk,delta8_zero ha R,ite_self,add_zero] at ne
  exact ne

private theorem y9_zero (D : RankData A b P) : y A 9=0 := by
  change (1:K)-nodes A 9=0
  simp [D.clockNine]

private theorem y_same {l k : Fin 10} (t : SameTag A l k) : y A l=y A k := by
  change (1:K)-nodes A l=1-nodes A k
  rw [t.1]

private theorem transpose_later (ha : ∀ i j, i≤j → A i j=0) (w : Fin 10 → K) (k : Fin 10) :
    (A.transpose *ᵥ w) k = ∑ l ∈ (Finset.univ.filter (fun l : Fin 10 => k<l)), A l k * w l := by
  rw [Matrix.mulVec,dotProduct,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : k<l
  · simp [h]
  · simp [h,ha l k (le_of_not_gt h)]

private theorem later7 : (Finset.univ.filter (fun l : Fin 10 => (7:Fin 10)<l)) = {8,9} := by
  ext l
  fin_cases l <;> decide

private theorem later6 : (Finset.univ.filter (fun l : Fin 10 => (6:Fin 10)<l)) = {7,8,9} := by
  ext l
  fin_cases l <;> decide

private theorem later8 : (Finset.univ.filter (fun l : Fin 10 => (8:Fin 10)<l)) = {9} := by
  ext l
  fin_cases l <;> decide

private theorem J_at7 (ha : ∀ i j, i≤j → A i j=0) (D : RankData A b P)
    {k : ℕ} (kp : 0<k) :
    J A b k 7 = ((k+1:ℕ):K)*(A 8 7*(b 8*(y A 8)^k))-b 7*(y A 7)^(k+1) := by
  change ((k+1:ℕ):K)*((A.transpose *ᵥ reflectedStageWeight A b k) (7:Fin 10)) -
    b 7*(y A 7)^(k+1)=_
  rw [transpose_later ha,later7,Finset.sum_pair (by decide : (8:Fin 10)≠9)]
  change ((k+1:ℕ):K)*(A 8 7*(b 8*(y A 8)^k)+A 9 7*(b 9*(y A 9)^k)) -
    b 7*(y A 7)^(k+1)=_
  simp only [y9_zero D,zero_pow (ne_of_gt kp),mul_zero,add_zero]

private theorem J_at6 (ha : ∀ i j, i≤j → A i j=0) (D : RankData A b P)
    {k : ℕ} (kp : 0<k) :
    J A b k 6 =
      ((k+1:ℕ):K)*(A 7 6*(b 7*(y A 7)^k)+A 8 6*(b 8*(y A 8)^k))-b 6*(y A 6)^(k+1) := by
  change ((k+1:ℕ):K)*((A.transpose *ᵥ reflectedStageWeight A b k) (6:Fin 10)) -
    b 6*(y A 6)^(k+1)=_
  rw [transpose_later ha,later6,
    Finset.sum_insert (by decide : (7:Fin 10)∉({8,9}:Finset (Fin 10))),
    Finset.sum_pair (by decide : (8:Fin 10)≠9)]
  change ((k+1:ℕ):K)*(A 7 6*(b 7*(y A 7)^k)+
    (A 8 6*(b 8*(y A 8)^k)+A 9 6*(b 9*(y A 9)^k))) - b 6*(y A 6)^(k+1)=_
  simp only [y9_zero D,zero_pow (ne_of_gt kp),mul_zero,add_zero]

private theorem J_at8 (ha : ∀ i j, i≤j → A i j=0) (D : RankData A b P)
    {k : ℕ} (kp : 0<k) :
    J A b k 8=-(b 8*(y A 8)^(k+1)) := by
  change ((k+1:ℕ):K)*((A.transpose *ᵥ reflectedStageWeight A b k) (8:Fin 10)) -
    b 8*(y A 8)^(k+1)=_
  rw [transpose_later ha,later8,Finset.sum_singleton]
  change ((k+1:ℕ):K)*(A 9 8*(b 9*(y A 9)^k))-b 8*(y A 8)^(k+1)=_
  simp only [y9_zero D,zero_pow (ne_of_gt kp),mul_zero,zero_sub]

private theorem quad_at_early (R : RepeatAtEight A b i) {k : Fin 10} (kk : k<8) :
    J A b 1 k=if k=i then b 8*(y A 8)^2 else 0 := by
  change quadraticSeed A b k=_
  rw [R.quad,Pi.smul_apply,smul_eq_mul]
  by_cases e : k=i
  · subst k
    simp [contrast_early (ne_of_lt kk)]
  · rw [contrast_other e (ne_of_lt kk),mul_zero,if_neg e]

private theorem off_seed_offsets (D : RankData A b P) (R : RepeatAtEight A b i)
    {k : Fin 10} (kk : k<8) (gk : g A k≠0) :
    J A b 1 k= -(b k*(y A k)^2) ∧ y A 8*J A b 1 k+b k*(y A k)^3=0 := by
  have m := D.cancel (nodes A k) (mem_offKnots.mpr ⟨k,gk,rfl⟩)
  rw [offMass_at_early R b kk gk] at m
  have q := quad_at_early R kk
  by_cases e : k=i
  · have yy : y A k=y A 8 := by subst k; exact y_same R.same
    rw [if_pos e] at q m
    rw [q,yy]
    constructor
    · linear_combination (y A 8)^2*m
    · linear_combination (y A 8)^3*m
  · rw [if_neg e] at q m
    have bk : b k=0 := by simpa using m
    simp [q,bk]

private theorem cubic_line (D : RankData A b P) (R : RepeatAtEight A b i)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) :
    ∃ ξ : K, J A b 2-y A 8 • J A b 1=ξ • Δ A i := by
  let V := annih (treeSpace A 4)
  have q1 : J A b 1∈V := reflectedStageRow_annih ho 4 1 (by decide)
  have q2 : J A b 2∈V := reflectedStageRow_annih ho 4 2 (by decide)
  have m : J A b 2-y A 8 • J A b 1∈annih (treeSpace A 4) :=
    V.sub_mem q2 (V.smul_mem _ q1)
  rw [R.reverseSpace,Submodule.mem_sup] at m
  obtain ⟨a,am,d,dm,eq⟩ := m
  obtain ⟨coef,rfl⟩ := Submodule.mem_span_singleton.mp am
  obtain ⟨ξ,rfl⟩ := Submodule.mem_span_singleton.mp dm
  have t := congrFun eq (8:Fin 10)
  change coef*contrast K i 8 8+ξ*Δ A i 8 = J A b 2 8-y A 8*J A b 1 8 at t
  rw [contrast_late (ne_of_lt R.before),delta8_zero ha R,mul_one,mul_zero,add_zero,
    J_at8 ha D (k:=2) (by decide),J_at8 ha D (k:=1) (by decide)] at t
  have z : coef=0 := by linear_combination t
  exact ⟨ξ,by simpa only [z,zero_smul,zero_add] using eq.symm⟩

private theorem delta_at7 (ha : ∀ i j, i≤j → A i j=0) (R : RepeatAtEight A b i) :
    Δ A i 7=A 8 7 := by
  have bnd := R.before
  have il : i≤(7:Fin 10) := by omega
  change mat A.transpose (contrast K i 8) (7:Fin 10)=A 8 7
  rw [transpose_contrast_apply,ha i 7 il,sub_zero]

theorem row7_clean (D : RankData A b P) (R : RepeatAtEight A b i)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) : g A 7=0 := by
  by_contra off
  have paid := (off_seed_offsets D R (by decide : (7:Fin 10)<8) off).1
  have ne := delta_early_off_nonzero ha R (by decide : (7:Fin 10)<8) off
  rw [delta_at7 ha R] at ne
  rw [J_at7 ha D (k:=1) (by decide)] at paid
  change (2:K)*(A 8 7*(b 8*(y A 8)^1))-b 7*(y A 7)^2= -(b 7*(y A 7)^2) at paid
  simp only [pow_one] at paid
  have x : (2:K)*A 8 7*(b 8*y A 8)=0 := by linear_combination paid
  exact (mul_ne_zero (mul_ne_zero (two_ne ho) ne) (mul_ne_zero R.liveEight R.reflEight)) x

theorem row6_clean (D : RankData A b P) (R : RepeatAtEight A b i)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) : g A 6=0 := by
  by_contra off
  have g7 := row7_clean D R ha ho
  obtain ⟨ξ,rev⟩ := cubic_line D R ha ho
  have d6 := delta_early_off_nonzero ha R (by decide : (6:Fin 10)<8) off
  have b6 := off_seed_offsets D R (by decide : (6:Fin 10)<8) off
  have j16 := J_at6 ha D (k:=1) (by decide)
  have j26 := J_at6 ha D (k:=2) (by decide)
  have eq6 := congrFun rev (6:Fin 10)
  change J A b 2 6-y A 8*J A b 1 6=ξ*Δ A i 6 at eq6
  have a6 : A 7 6*(b 7*y A 7)+A 8 6*(b 8*y A 8)=0 := by
    change J A b 1 6=(2:K)*(A 7 6*(b 7*(y A 7)^1)+A 8 6*(b 8*(y A 8)^1))-
      b 6*(y A 6)^2 at j16
    simp only [pow_one] at j16
    have zz : (2:K)*(A 7 6*(b 7*y A 7)+A 8 6*(b 8*y A 8))=0 := by
      linear_combination b6.1-j16
    exact (mul_eq_zero.mp zz).resolve_left (two_ne ho)
  have c6 : (3:K)*(A 7 6*(b 7*(y A 7)^2)+A 8 6*(b 8*(y A 8)^2))=ξ*Δ A i 6 := by
    change J A b 2 6=(3:K)*(A 7 6*(b 7*(y A 7)^2)+A 8 6*(b 8*(y A 8)^2))-
      b 6*(y A 6)^3 at j26
    linear_combination eq6-j26+b6.2
  have z7 : y A 7≠0 := by
    intro z
    have e : nodes A 7=1 := (sub_eq_zero.mp z).symm
    exact (by decide : (7:Fin 10)≠9) (D.uniqueOne 7 g7 e)
  have mass := D.cleanMassNe (nodes A 7) (mem_cleanKnots.mpr ⟨7,g7,rfl⟩)
  rw [cleanMass_at_early R b (by decide : (7:Fin 10)<8) g7] at mass
  have j17 := J_at7 ha D (k:=1) (by decide)
  have j27 := J_at7 ha D (k:=2) (by decide)
  have eq7 := congrFun rev (7:Fin 10)
  change J A b 2 7-y A 8*J A b 1 7=ξ*Δ A i 7 at eq7
  rw [delta_at7 ha R] at eq7
  have s7 := quad_at_early R (by decide : (7:Fin 10)<8)
  change J A b 1 7=(2:K)*(A 8 7*(b 8*(y A 8)^1))-b 7*(y A 7)^2 at j17
  simp only [pow_one] at j17
  change J A b 2 7=(3:K)*(A 8 7*(b 8*(y A 8)^2))-b 7*(y A 7)^3 at j27
  by_cases e : (7:Fin 10)=i
  · have yy : y A 7=y A 8 := by rw [e]; exact y_same R.same
    simp only [if_pos e] at s7 mass
    have a7 : (2:K)*A 8 7*(b 8*y A 8)=(b 7+b 8)*(y A 8)^2 := by
      rw [yy] at j17
      linear_combination s7-j17
    have ae : A 8 7≠0 := by
      intro z
      rw [z,mul_zero,zero_mul] at a7
      exact (mul_ne_zero mass (pow_ne_zero _ R.reflEight)) a7.symm
    have xi : ξ=b 8*(y A 8)^2 := by
      have X : (ξ-b 8*(y A 8)^2)*A 8 7=0 := by
        rw [s7] at eq7
        rw [yy] at j27
        linear_combination -eq7+j27+(y A 8)*a7
      exact sub_eq_zero.mp ((mul_eq_zero.mp X).resolve_right ae)
    rw [yy] at a6 c6
    have kill : ξ*Δ A i 6=0 := by
      linear_combination -c6+3*(y A 8)*a6
    exact (mul_ne_zero (by rw [xi]; exact mul_ne_zero R.liveEight (pow_ne_zero _ R.reflEight)) d6) kill
  · simp only [if_neg e,add_zero] at s7 mass
    have a7 : (2:K)*A 8 7*(b 8*y A 8)=b 7*(y A 7)^2 := by
      linear_combination s7-j17
    have ae : A 8 7≠0 := by
      intro z
      rw [z,mul_zero,zero_mul] at a7
      exact (mul_ne_zero mass (pow_ne_zero _ z7)) a7.symm
    have xi : ξ=b 8*y A 8*(3*y A 8-2*y A 7) := by
      have X : (ξ-b 8*y A 8*(3*y A 8-2*y A 7))*A 8 7=0 := by
        linear_combination -eq7+j27-(y A 8)*s7+(y A 7)*a7
      exact sub_eq_zero.mp ((mul_eq_zero.mp X).resolve_right ae)
    have t := R.before
    have il : i≤(6:Fin 10) := by omega
    have dA : Δ A i 6=A 8 6 := by
      change mat A.transpose (contrast K i 8) (6:Fin 10)=A 8 6
      rw [transpose_contrast_apply,ha i 6 il,sub_zero]
    rw [dA,xi] at c6
    have z : b 8*y A 8*y A 7*A 8 6=0 := by
      linear_combination 3*(y A 7)*a6-c6
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero R.liveEight R.reflEight) z7)
      (dA ▸ d6)) z

end RKResearch.Certified.Graded.FourOffPhysical
