module

public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exactly the seven quartic tent exceptions above total eight

Source-only, independent of Matrix.Rank and any earlier central-window
bound. These are abstract normal-index digits, not fixed masks. -/
namespace RKResearch.Certified.Graded.HankelQuarticFullProfile

/-- Read `n` consecutive heights beginning a single step after `r`. -/
def heights (ν : ℕ → ℕ) (r : ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => ν (r+1) :: heights ν (r+1) n

def tent (g l : ℕ) : List ℕ := heights (fun q => min q (g-q)) 0 l

/-- Observable prefixes of complete or truncated tents of length ≤5. -/
def profiles : ℕ → ℕ → List (List ℕ)
  | 0, n => if n=0 then [[]] else []
  | fuel+1, n =>
    if n=0 then [[]] else
      (List.range 5).flatMap fun k =>
        let g := k+1
        if n≤g then [tent g n]
        else (profiles fuel (n-g)).map (fun s => tent g g ++ s)

/-- The full eight digits at widths 1 to 8, not the central six. -/
def badProfiles : List (List ℕ) :=
  [[1,2,2,1,0,1,2,2], [1,2,1,0,1,2,2,1], [1,2,2,1,0,1,2,1],
   [0,1,2,1,0,1,2,2], [0,1,2,2,1,0,1,2], [1,2,1,0,0,1,2,2],
   [1,2,2,1,0,0,1,2]]

private theorem heights_append (ν : ℕ → ℕ) (r m n : ℕ) :
    heights ν r (m+n) = heights ν r m ++ heights ν (r+m) n := by
  induction m generalizing r with
  | zero => simp [heights]
  | succ m ih =>
    simp only [Nat.succ_add,heights,List.cons_append,ih]
    rw [show (r+m).succ = r+(m+1) by omega]

private theorem heights_congr {ν τ : ℕ → ℕ} {r s n : ℕ}
    (h : ∀ i, 0<i → i≤n → ν (r+i)=τ (s+i)) :
    heights ν r n = heights τ s n := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih =>
    change ν (r+1) :: heights ν (r+1) n = τ (s+1) :: heights τ (s+1) n
    rw [h 1 (by omega) (by omega)]
    congr 1
    apply ih
    intro i ip il
    have eq := h (i+1) (by omega) (by omega)
    rwa [show r+1+i = r+(i+1) by omega, show s+1+i = s+(i+1) by omega]

/-- Exact visible tents starting at each paid nonsingular width. -/
def RestartsThrough (ν : ℕ → ℕ) (W : ℕ) : Prop :=
  ∀ r < W, ν r = 0 →
    ∃ g, 0 < g ∧ ∀ q, q ≤ g → r+q ≤ W →
      ν (r+q) = min q (g-q)

private theorem bounded_restart {ν : ℕ → ℕ} (cap : ∀ w ≤ 8, ν w ≤ 2)
    (step : RestartsThrough ν 8) {r : ℕ} (r8 : r<8) (zr : ν r=0) :
    ∃ g, 0<g ∧ g≤5 ∧ ∀ q, q≤g → r+q≤8 → ν (r+q)=min q (g-q) := by
  obtain ⟨g,gp,h⟩ := step r r8 zr
  by_cases g5 : g ≤ 5
  · exact ⟨g,gp,g5,h⟩
  have near : 8 < r+3 := by
    by_contra nope
    have e := h 3 (by omega) (by omega)
    have paid : (3 : ℕ)+3≤g := by omega
    have mg : min 3 (g-3) = 3 := Nat.min_eq_left (Nat.le_sub_of_add_le paid)
    rw [mg] at e
    have le := cap (r+3) (by omega)
    omega
  refine ⟨5,by decide,Nat.le_refl 5,?_⟩
  intro q _ rq
  have q2 : q≤2 := by omega
  have hg : q+q≤g := by omega
  have h5 : q+q≤5 := by omega
  rw [h q (by omega) rq, Nat.min_eq_left (Nat.le_sub_of_add_le hg),
    Nat.min_eq_left (Nat.le_sub_of_add_le h5)]

private theorem heights_eq_tent {ν : ℕ → ℕ} {r g l : ℕ}
    (h : ∀ i, 0<i → i≤l → ν (r+i)=min i (g-i)) :
    heights ν r l = tent g l := by
  unfold tent
  apply heights_congr
  intro i ip il
  simpa only [zero_add] using h i ip il

private theorem heights_mem_profiles {ν : ℕ → ℕ}
    (bounded : ∀ r < 8, ν r=0 → ∃ g, 0<g ∧ g≤5 ∧
      ∀ q, q≤g → r+q≤8 → ν (r+q)=min q (g-q)) :
    ∀ fuel r n, n≤fuel → r+n≤8 → ν r=0 →
      heights ν r n ∈ profiles fuel n := by
  intro fuel
  induction fuel with
  | zero =>
    intro r n hn _ _
    have : n=0 := by omega
    subst n
    simp [heights,profiles]
  | succ fuel ih =>
    intro r n hn rn hr
    by_cases nz : n=0
    · subst n
      simp [heights,profiles]
    obtain ⟨g,gp,g5,h⟩ := bounded r (by omega) hr
    simp only [profiles,if_neg nz,List.mem_flatMap]
    refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
    rw [show g-1+1=g by omega]
    by_cases ng : n≤g
    · rw [if_pos ng,List.mem_singleton]
      exact heights_eq_tent fun i _ hi => h i (by omega) (by omega)
    · rw [if_neg ng,List.mem_map]
      have hzero : ν (r+g)=0 := by rw [h g (Nat.le_refl g) (by omega),Nat.sub_self,Nat.min_zero]
      have rest := ih (r+g) (n-g) (by omega) (by omega) hzero
      have lead : heights ν r g = tent g g :=
        heights_eq_tent fun i _ hi => h i hi (by omega)
      refine ⟨heights ν (r+g) (n-g),rest,?_⟩
      rw [← lead, ← heights_append,show g+(n-g)=n by omega]

set_option maxRecDepth 4096 in
private theorem full_profile_check :
    (profiles 8 8).all (fun s => decide (s.sum ≤ 8 ∨ s ∈ badProfiles)) = true := by
  decide +kernel

/-- The pure actual-mask proof needs to exclude precisely these seven
possibilities. No untested future width is added by the classification. -/
theorem full_profile_small_or_exception (ν : ℕ → ℕ) (start : ν 0=0)
    (cap : ∀ w ≤ 8, ν w≤2) (restart : RestartsThrough ν 8) :
    (heights ν 0 8).sum ≤ 8 ∨ heights ν 0 8 ∈ badProfiles := by
  have seen := heights_mem_profiles (ν := ν)
    (fun r r8 zr => bounded_restart cap restart r8 zr) 8 0 8 (Nat.le_refl 8) (by decide) start
  exact of_decide_eq_true (List.all_eq_true.mp full_profile_check _ seen)

theorem full_nullity_le_eight_of_no_exception (ν : ℕ → ℕ) (start : ν 0=0)
    (cap : ∀ w ≤ 8, ν w≤2) (restart : RestartsThrough ν 8)
    (no : heights ν 0 8 ∉ badProfiles) :
    ν 1 + ν 2 + ν 3 + ν 4 + ν 5 + ν 6 + ν 7 + ν 8 ≤ 8 := by
  have h := (full_profile_small_or_exception ν start cap restart).resolve_right no
  simpa only [heights,List.sum_cons,List.sum_nil,add_zero,Nat.add_assoc] using h

end RKResearch.Certified.Graded.HankelQuarticFullProfile
