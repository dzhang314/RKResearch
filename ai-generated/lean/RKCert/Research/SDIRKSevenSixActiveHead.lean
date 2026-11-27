module

public import RKCert.Research.SDIRKSevenSixActiveQuadratic
public import RKCert.Research.SDIRKSevenTailCubicPurity
public import RKCert.Research.SDIRKSevenEightStageGhostExclusion
public import RKCert.Research.SDIRKSixTailScalarObstruction

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Folding the tied helper and exposing the nonzero-seed head -/
namespace RKResearch.Certified.SDIRKSevenSixActive
open RKResearch Graded SDIRKSevenTailCollision FiniteRootedTree
open scoped Matrix BigOperators Classical

noncomputable section

variable {R : Type*} [CommRing R] {n p : ℕ}

private def merge (j : Fin (n+1)) (r : Fin n) (w : Fin (n+1)→R) : Fin n→R :=
  fun k => w (j.succAbove k) + if k=r then w j else 0

private theorem sum_merge (j : Fin (n+1)) (r : Fin n) (w v : Fin (n+1)→R)
    (hv : v j=v (j.succAbove r)) :
    (∑ k, merge j r w k*v (j.succAbove k))=(∑ k,w k*v k) := by
  classical
  simp only [merge,add_mul,Finset.sum_add_distrib]
  rw [Fin.sum_univ_succAbove _ j,add_comm]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp [hv]
  · intro k _ hk; simp [hk]
  · simp

/-- Folding a pair of implicit stages requires equality of the
incoming rows after the two diagonal coordinates are identified, not
literal equality of the two physical rows. -/
theorem implicit_fold {A : Matrix (Fin (n+1)) (Fin (n+1)) R} {b : Fin (n+1)→R} {γ : R}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ)
    {i j : Fin (n+1)} (hij : i<j) (tap : A j i=0)
    (eq : ∀ k, k≠i → k≠j → A i k=A j k) (bi : b i=0) (bj : b j=0) :
    ∃ (B : Matrix (Fin n) (Fin n) R) (w : Fin n→R),
      HasOrder p B w ∧ B.IsLowerTriangular ∧ (∀ k,B k k=γ) ∧ ∃ k,w k=0 := by
  obtain ⟨r,hr⟩ := Fin.exists_succAbove_eq (ne_of_lt hij)
  have folded : merge j r (A i)=merge j r (A j) := by
    funext k
    by_cases e : k=r
    · subst k
      simp only [merge,ite_true,hr,he,ha hij,tap,add_zero,zero_add]
    · have hki : j.succAbove k≠i := fun h => e (Fin.succAbove_right_injective (h.trans hr.symm))
      simp only [merge,ite_false,e,add_zero]
      exact eq _ hki (Fin.succAbove_ne _ _)
  have same (t : FiniteRootedTree) : Φ t A i=Φ t A j := by
    induction t with
    | leaf => rfl
    | butcherProduct t u ht hu =>
      change Φ t A i*(∑ k,A i k*Φ u A k)=Φ t A j*(∑ k,A j k*Φ u A k)
      rw [←sum_merge j r (A i) _ (by rw [hr]; exact hu.symm),
        ←sum_merge j r (A j) _ (by rw [hr]; exact hu.symm),folded,ht]
  let B : Matrix (Fin n) (Fin n) R := fun a => merge j r (A (j.succAbove a))
  let w : Fin n→R := merge j r b
  have st (t : FiniteRootedTree) (k : Fin n) : Φ t B k=Φ t A (j.succAbove k) := by
    induction t generalizing k with
    | leaf => rfl
    | butcherProduct t u ht hu =>
      change Φ t B k*(∑ l,B k l*Φ u B l)=Φ t A (j.succAbove k)*(∑ l,A (j.succAbove k) l*Φ u A l)
      rw [ht]
      congr 1
      rw [←sum_merge j r (A (j.succAbove k)) _ (by rw [hr]; exact (same u).symm)]
      apply Finset.sum_congr rfl
      intro l _
      rw [hu]
  refine ⟨B,w,?_,?_,?_,⟨r,?_⟩⟩
  · intro t ht
    change (t.factorial:R)*(∑ k,w k*Φ t B k)=1
    simp only [st,w,sum_merge j r b _ (by rw [hr]; exact (same t).symm)]
    exact ho t ht
  · intro x y hxy
    have h := (Fin.succAboveOrderEmb j).strictMono hxy
    change j.succAbove x < j.succAbove y at h
    by_cases e : y=r
    · subst y
      have hj' : j.succAbove x < j := h.trans (hr.symm ▸ hij)
      have h₁ : A (j.succAbove x) (j.succAbove r)=0 := ha h
      have h₂ : A (j.succAbove x) j=0 := ha hj'
      simp [B,merge,h₁,h₂]
    · have h₁ : A (j.succAbove x) (j.succAbove y)=0 := ha h
      simp [B,merge,h₁,e]
  · intro k
    by_cases e : k=r
    · subst k; simp [B,merge,hr,he,ha hij]
    · simp [B,merge,he,e]
  · simp [w,merge,hr,bi,bj]

section Head
variable {K : Type*} [Field K]
variable {A : Matrix F F K} {γ : K}

private theorem row0 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (v : F→K) :
    mat A v 0=γ*v 0 := by
  change (∑ j : F,A 0 j*v j)=_
  rw [Finset.sum_eq_single (0:F),he]
  · intro i _ hi
    have z : A 0 i=0 := @ha (0:F) i (Fin.pos_iff_ne_zero.mpr hi)
    rw [z,zero_mul]
  · simp

private theorem row1 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (v : F→K) :
    mat A v 1=A 1 0*v 0+γ*v 1 := by
  change (∑ j : F,A 1 j*v j)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 1 0*v 0+(A 1 1*v 1+∑ j : Fin 7,A 1 j.succ.succ*v j.succ.succ)=_
  have z : (∑ j : Fin 7,A 1 j.succ.succ*v j.succ.succ)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have h : (1:F)<j.succ.succ := by change 1<j.val+1+1; omega
    have e : A 1 j.succ.succ=0 := @ha (1:F) j.succ.succ h
    rw [e,zero_mul]
  rw [z,he,add_zero]

private theorem row2 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (v : F→K) :
    mat A v 2=A 2 0*v 0+A 2 1*v 1+γ*v 2 := by
  change (∑ j : F,A 2 j*v j)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 2 0*v 0+(A 2 1*v 1+(A 2 2*v 2+∑ j : Fin 6,
    A 2 j.succ.succ.succ*v j.succ.succ.succ))=_
  have z : (∑ j : Fin 6,A 2 j.succ.succ.succ*v j.succ.succ.succ)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have h : (2:F)<j.succ.succ.succ := by change 2<j.val+1+1+1; omega
    have e : A 2 j.succ.succ.succ=0 := @ha (2:F) j.succ.succ.succ h
    rw [e,zero_mul]
  rw [z,he,add_zero]; ring

private theorem c0 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    nodes A 0=γ := by change mat A 1 0=_; rw [row0 ha he]; simp

private theorem c1 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    nodes A 1=A 1 0+γ := by change mat A 1 1=_; rw [row1 ha he]; simp

private theorem c2 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    nodes A 2=A 2 0+A 2 1+γ := by change mat A 1 2=_; rw [row2 ha he]; simp

private def g (A : Matrix F F K) : F→K := monomialStageDefect A 1

private theorem g0 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) : g A 0=γ^2 := by
  change ((1+1:ℕ):K)*mat A (fun i=> (nodes A i)^1) 0-(nodes A 0)^(1+1)=_
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one]
  rw [row0 ha he,c0 ha he]; ring

private theorem g1 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    g A 1=γ^2+2*γ*A 1 0-(A 1 0)^2 := by
  change ((1+1:ℕ):K)*mat A (fun i=> (nodes A i)^1) 1-(nodes A 1)^(1+1)=_
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one]
  rw [row1 ha he,c0 ha he,c1 ha he]; ring

private theorem gAt2 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    g A 2=4*γ*nodes A 2-2*γ^2-(nodes A 2)^2+2*A 1 0*A 2 1 := by
  change ((1+1:ℕ):K)*mat A (fun i=> (nodes A i)^1) 2-(nodes A 2)^(1+1)=_
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one]
  rw [row2 ha he,c0 ha he,c1 ha he,c2 ha he]; ring

end Head

private theorem head_cases (i : F) (hi : i∉tail) : i=0 ∨ i=1 ∨ i=2 := by
  have h : i.val<3 := Nat.lt_of_not_ge (fun x=>hi (mem_tail.mpr x))
  have e : i.val=0 ∨ i.val=1 ∨ i.val=2 := by omega
  exact e.imp Fin.ext (fun r=>r.imp Fin.ext Fin.ext)

private theorem head_coeff₁ {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hz : ∀ i, i∉tail → b i=0) : A 1 0≠0 := by
  intro tap
  have eq (k : F) (hki : k≠0) (hkj : k≠1) : A 0 k=A 1 k := by
    have h : (1:F)<k := by
      have e₀ : k.val≠0 := fun e=>hki (Fin.ext e)
      have e₁ : k.val≠1 := fun e=>hkj (Fin.ext e)
      change 1<k.val
      omega
    have e₀ : A 0 k=0 := @ha (0:F) k ((by decide : (0:F)<1).trans h)
    have e₁ : A 1 k=0 := @ha (1:F) k h
    rw [e₀,e₁]
  obtain ⟨B,w,hB,lo,diag,i,hi⟩ := implicit_fold ho ha he (by decide : (0:F)<1)
    tap eq (hz 0 (by decide)) (hz 1 (by decide))
  exact Graded.SDIRKSeven.rational_all_weights_ne_zero hB lo diag hγ i hi

private theorem helper_distinct_or_tap {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hz : ∀ i, i∉tail → b i=0)
    (collision : nodes A 2=nodes A 0 ∨ nodes A 2=nodes A 1) : A 2 1≠0 := by
  intro tap
  rcases collision with e | e
  · have t20 : A 2 0=0 := by
      rw [c2 ha he,c0 ha he,tap] at e; linear_combination e
    have eq (k : F) (hki : k≠0) (hkj : k≠2) : A 0 k=A 2 k := by
      by_cases h : k=1
      · subst k
        rw [tap]
        exact @ha (0:F) (1:F) (by decide)
      have hgt : (2:F)<k := by
        have e₀ : k.val≠0 := fun e=>hki (Fin.ext e)
        have e₁ : k.val≠1 := fun e=>h (Fin.ext e)
        have e₂ : k.val≠2 := fun e=>hkj (Fin.ext e)
        change 2<k.val; omega
      have e₀ : A 0 k=0 := @ha (0:F) k ((by decide : (0:F)<2).trans hgt)
      have e₂ : A 2 k=0 := @ha (2:F) k hgt
      rw [e₀,e₂]
    obtain ⟨B,w,hB,lo,diag,i,hi⟩ := implicit_fold ho ha he (by decide : (0:F)<2)
      t20 eq (hz 0 (by decide)) (hz 2 (by decide))
    exact Graded.SDIRKSeven.rational_all_weights_ne_zero hB lo diag hγ i hi
  · have t20 : A 2 0=A 1 0 := by
      rw [c2 ha he,c1 ha he,tap] at e; linear_combination e
    have eq (k : F) (hki : k≠1) (hkj : k≠2) : A 1 k=A 2 k := by
      by_cases h : k=0
      · subst k; exact t20.symm
      have hgt : (2:F)<k := by
        have e₀ : k.val≠0 := fun e=>h (Fin.ext e)
        have e₁ : k.val≠1 := fun e=>hki (Fin.ext e)
        have e₂ : k.val≠2 := fun e=>hkj (Fin.ext e)
        change 2<k.val; omega
      have e₀ : A 1 k=0 := @ha (1:F) k ((by decide : (1:F)<2).trans hgt)
      have e₂ : A 2 k=0 := @ha (2:F) k hgt
      rw [e₀,e₂]
    obtain ⟨B,w,hB,lo,diag,i,hi⟩ := implicit_fold ho ha he (by decide : (1:F)<2)
      tap eq (hz 1 (by decide)) (hz 2 (by decide))
    exact Graded.SDIRKSeven.rational_all_weights_ne_zero hB lo diag hγ i hi

section Expose
variable {K : Type*} [Field K] {A : Matrix F F K}

private theorem axis_from_supported {m : ℕ} {v : F→K}
    (hv : v∈zeroSpace A m) (i : F) (nz : v i≠0) (z : ∀ j,j≠i → v j=0) :
    Pi.single i (1:K)∈zeroSpace A m := by
  have e : (Pi.single i (1:K))=(v i)⁻¹ • v := by
    funext j
    by_cases h : j=i
    · subst j; simp [inv_mul_cancel₀ nz]
    · simp [Pi.single_eq_of_ne h,z j h]
  rw [e]; exact (zeroSpace A m).smul_mem _ hv

private theorem replace_g_two {m : ℕ} (hm : 3≤m) {v : F→K}
    (hv : v∈zeroSpace A 2 ∨ v∈zeroSpace A 3)
    (hCv : diag (nodes A) v∈zeroSpace A m)
    (rest : ∀ i,i≠0 → i≠1 → v i=0)
    (v₀ : v 0≠0) (v₁ : v 1≠0) (c01 : nodes A 0≠nodes A 1) :
    (Pi.single (0:F) (1:K))∈zeroSpace A m ∧ (Pi.single (1:F) (1:K))∈zeroSpace A m := by
  have hV : v∈zeroSpace A m := hv.elim (fun h => zeroSpace_mono A (by omega) h) (fun h => zeroSpace_mono A hm h)
  constructor
  · let V := diag (nodes A) v-(nodes A 1) • v
    have eq (i : F) : V i=(nodes A i-nodes A 1)*v i := by
      simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply]; ring
    have hp : V∈zeroSpace A m := (zeroSpace A m).sub_mem hCv ((zeroSpace A m).smul_mem _ hV)
    apply axis_from_supported hp 0
    · rw [eq]; exact mul_ne_zero (sub_ne_zero.mpr c01) v₀
    · intro i hi
      by_cases h : i=1
      · simp [eq,h]
      · simp [eq,rest i hi h]
  · let V := diag (nodes A) v-(nodes A 0) • v
    have eq (i : F) : V i=(nodes A i-nodes A 0)*v i := by
      simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply]; ring
    have hp : V∈zeroSpace A m := (zeroSpace A m).sub_mem hCv ((zeroSpace A m).smul_mem _ hV)
    apply axis_from_supported hp 1
    · rw [eq]; exact mul_ne_zero (sub_ne_zero.mpr c01.symm) v₁
    · intro i hi
      by_cases h : i=0
      · simp [eq,h]
      · simp [eq,rest i h hi]

private theorem head_paid_of_collision {i j : F}
    (hj : ∀ k,k∉tail → k=i ∨ k=j ∨ k=2) (h10 : i≠j) (hi : i≠2) (hj2 : j≠2)
    (hc : nodes A 2=nodes A i) (d : nodes A j≠nodes A i)
    (diff : g A 2≠g A i) (nz₂ : g A 2≠0)
    (nz₀ : g A 0≠0) (nz₁ : g A 1≠0) (c01 : nodes A 0≠nodes A 1)
    (clean : ∀ k∈tail,g A k=0) : SDIRKSevenTailCubicPurity.PaidHead A := by
  let G := g A
  let a := (G j-G i)/(nodes A j-nodes A i)
  let V := G*G-(G i) • G-a • (diag (nodes A) G-(nodes A i) • G)
  have gv : G∈zeroSpace A 2 := monomialStageDefect_mem A 1
  have cv := diag_zeroSpace A 2 gv
  have gz : G∈zeroSpace A 4 := zeroSpace_mono A (by decide) gv
  have vp : V∈zeroSpace A 4 :=
    (zeroSpace A 4).sub_mem ((zeroSpace A 4).sub_mem (zeroSpace_mul gv gv)
      ((zeroSpace A 4).smul_mem _ gz)) ((zeroSpace A 4).smul_mem _
      ((zeroSpace A 4).sub_mem (zeroSpace_mono A (by decide) cv) ((zeroSpace A 4).smul_mem _ gz)))
  have ev (k : F) : V k=G k*((G k-G i)-a*(nodes A k-nodes A i)) := by
    simp only [V,Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,diag_apply]
    ring
  have single₂ : Pi.single (2:F) (1:K)∈zeroSpace A 4 := by
    apply axis_from_supported vp 2
    · rw [ev,hc,sub_self,mul_zero,sub_zero]
      exact mul_ne_zero nz₂ (sub_ne_zero.mpr diff)
    · intro k hk
      rw [ev]
      by_cases h : k∈tail
      · rw [show G k=0 from clean k h,zero_mul]
      rcases hj k h with rfl | rfl | rfl
      · simp
      · rw [show a*(nodes A k-nodes A i)=G k-G i from div_mul_cancel₀ _ (sub_ne_zero.mpr d)]
        simp
      · exact (hk rfl).elim
  let W := G-(G 2) • (Pi.single (2:F) (1:K))
  have w4 : W∈zeroSpace A 4 := (zeroSpace A 4).sub_mem gz ((zeroSpace A 4).smul_mem _ single₂)
  have w₀ : W 0=G 0 := by simp [W]
  have w₁ : W 1=G 1 := by simp [W]
  have cw : diag (nodes A) W∈zeroSpace A 4 := by
    have e : diag (nodes A) W = diag (nodes A) G - ((G 2)*nodes A 2) • Pi.single (2:F) 1 := by
      funext k
      by_cases h : k=2
      · subst k; simp [W,diag_apply]
        ring
      · simp [W,diag_apply,Pi.single_eq_of_ne h]
    rw [e]
    exact (zeroSpace A 4).sub_mem (zeroSpace_mono A (by decide) cv) ((zeroSpace A 4).smul_mem _ single₂)
  have rest (k : F) (k₀ : k≠0) (k₁ : k≠1) : W k=0 := by
    by_cases h : k∈tail
    · have e : k≠2 := fun e=> (by decide : (2:F)∉tail) (e ▸ h)
      simp [W,Pi.single_eq_of_ne e,show G k=0 from clean k h]
    · rcases head_cases k h with a | b | rfl
      · exact (k₀ a).elim
      · exact (k₁ b).elim
      · simp [W]
  have e (a b : F) (ne : a≠b) (s : nodes A a≠nodes A b)
      (Vₙ : W a≠0) (outside : ∀ k,k≠a → k≠b → W k=0) :
      Pi.single a (1:K)∈zeroSpace A 4 := by
    let X := diag (nodes A) W-(nodes A b) • W
    have e (k : F) : X k=(nodes A k-nodes A b)*W k := by
      simp only [X,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply]; ring
    have hp : X∈zeroSpace A 4 := (zeroSpace A 4).sub_mem cw ((zeroSpace A 4).smul_mem _ w4)
    apply axis_from_supported hp a
    · rw [e]; exact mul_ne_zero (sub_ne_zero.mpr s) Vₙ
    · intro k h
      rw [e]
      by_cases k' : k=b
      · simp [k']
      · simp [outside k h k']
  intro k hk
  rcases head_cases k hk with rfl | rfl | rfl
  · exact e 0 1 (by decide) c01 (w₀ ▸ nz₀) rest
  · exact e 1 0 (by decide) c01.symm (w₁ ▸ nz₁) (fun k k₁ k₀=>rest k k₀ k₁)
  · exact single₂

end Expose

private theorem second_seed_ne {A : Matrix F F ℚ} {γ : ℚ}
    (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0) : g A 1≠0 := by
  intro nz
  have ns : ¬ IsSquare (2:ℚ) := (Rat.isSquare_natCast_iff (n:=2)).not.mpr Nat.prime_two.not_isSquare
  apply ns
  refine ⟨A 1 0/γ-1,?_⟩
  rw [g1 ha he] at nz
  field_simp
  linear_combination nz

/-- Even a clock collision does not keep a nonzero third quadratic
seed out of the actual grade-four defect space. -/
theorem rational_head_paid_of_third_seed
    {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hz : ∀ i, i∉tail → b i=0) (active : ∀ i∈tail,b i≠0)
    (inj : ∀ i j, i∈tail → j∈tail → nodes A i=nodes A j → i=j)
    (nz₂ : monomialStageDefect A 1 2≠0) : SDIRKSevenTailCubicPurity.PaidHead A := by
  have clean : ∀ i∈tail,g A i=0 :=
    quadratic_hidden ho tail (by decide +kernel) hz active inj (monomialStageDefect_mem A 1)
  have t := head_coeff₁ ho ha he hγ hz
  have c01 : nodes A 0≠nodes A 1 := by
    rw [c0 ha he,c1 ha he]
    intro eq; apply t; linear_combination -eq
  have n₀ : g A 0≠0 := by rw [g0 ha he]; exact pow_ne_zero 2 hγ
  have n₁ := second_seed_ne ha he hγ
  by_cases c20 : nodes A 2=nodes A 0
  · have k := helper_distinct_or_tap ho ha he hγ hz (Or.inl c20)
    have d : g A 2≠g A 0 := by
      rw [gAt2 ha he,g0 ha he,c20,c0 ha he]
      intro eq
      exact (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℚ)≠0) t) k) (by linear_combination eq)
    exact head_paid_of_collision (i:=0) (j:=1) head_cases (by decide) (by decide) (by decide)
      c20 c01.symm d nz₂ n₀ n₁ c01 clean
  by_cases c21 : nodes A 2=nodes A 1
  · have k := helper_distinct_or_tap ho ha he hγ hz (Or.inr c21)
    have d : g A 2≠g A 1 := by
      rw [gAt2 ha he,g1 ha he,c21,c1 ha he]
      intro eq
      exact (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℚ)≠0) t) k) (by linear_combination eq)
    exact head_paid_of_collision (i:=1) (j:=0)
      (fun i hi => by rcases head_cases i hi with a|b|c; exacts [Or.inr (Or.inl a),Or.inl b,Or.inr (Or.inr c)])
      (by decide) (by decide) (by decide) c21 c01 d nz₂ n₀ n₁ c01 clean
  apply headPaid_of_quadratic_clean_tail A clean
  · intro i j hi hj hn
    rcases head_cases i hi with rfl | rfl | rfl <;>
      rcases head_cases j hj with rfl | rfl | rfl <;>
      first | exact (hn rfl).elim | exact c01 | exact c01.symm | exact c20 | exact Ne.symm c20 |
        exact c21 | exact Ne.symm c21
  · intro i hi
    rcases head_cases i hi with rfl | rfl | rfl
    · exact n₀
    · exact n₁
    · exact nz₂

/-- In the degenerate third-seed case the first two axes are already
paid one grade earlier. -/
theorem rational_first_two_cubic_of_third_seed_zero
    {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hz : ∀ i, i∉tail → b i=0) (active : ∀ i∈tail,b i≠0)
    (inj : ∀ i j, i∈tail → j∈tail → nodes A i=nodes A j → i=j)
    (z₂ : monomialStageDefect A 1 2=0) :
      Pi.single (0:F) (1:ℚ)∈zeroSpace A 3 ∧ Pi.single (1:F) (1:ℚ)∈zeroSpace A 3 := by
  have clean : ∀ i∈tail,g A i=0 :=
    quadratic_hidden ho tail (by decide +kernel) hz active inj (monomialStageDefect_mem A 1)
  have t := head_coeff₁ ho ha he hγ hz
  have c01 : nodes A 0≠nodes A 1 := by
    rw [c0 ha he,c1 ha he]
    intro eq; apply t; linear_combination -eq
  have n₀ : g A 0≠0 := by rw [g0 ha he]; exact pow_ne_zero 2 hγ
  have n₁ := second_seed_ne ha he hγ
  have G : g A∈zeroSpace A 2 := monomialStageDefect_mem A 1
  apply replace_g_two (by decide) (Or.inl G) (diag_zeroSpace A 2 G) ?_ n₀ n₁ c01
  intro i h₀ h₁
  by_cases it : i∈tail
  · exact clean i it
  rcases head_cases i it with a | b | rfl
  · exact (h₀ a).elim
  · exact (h₁ b).elim
  · exact z₂

/-- The third chronological row cannot hide every cubic defect over Q. -/
theorem rational_third_cubic_nonzero
    {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    ∃ v∈zeroSpace A 3, v 2≠0 := by
  by_contra h
  push Not at h
  have h₀ := c2 ha he
  have hz : g A 2=0 := h _ (zeroSpace_mono A (by decide : 2≤3) (monomialStageDefect_mem A 1))
  have h₁ : 2*(A 2 0*γ+A 2 1*nodes A 1+γ*nodes A 2)-(nodes A 2)^2=0 := by
    change ((1+1:ℕ):ℚ)*mat A (fun i=> (nodes A i)^1) 2-(nodes A 2)^(1+1)=0 at hz
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at hz
    rw [row2 ha he,c0 ha he] at hz
    exact hz
  have h₂ := h _ (monomialStageDefect_mem A 2)
  change ((2+1:ℕ):ℚ)*mat A (fun i=> (nodes A i)^2) 2-(nodes A 2)^(2+1)=0 at h₂
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at h₂
  rw [row2 ha he,c0 ha he] at h₂
  have h₃ := h _ (mat_zeroSpace ho 2 (by decide) (monomialStageDefect_mem A 1))
  change mat A (g A) 2=0 at h₃
  have e₁ : g A 1=4*γ*nodes A 1-2*γ^2-(nodes A 1)^2 := by
    rw [g1 ha he,c1 ha he]
    ring
  have hzg : g A 2=0 := h _ (zeroSpace_mono A (by decide : 2≤3) (monomialStageDefect_mem A 1))
  rw [row2 ha he,g0 ha he,e₁,hzg,mul_zero,add_zero] at h₃
  apply SDIRKSixTailScalarObstruction.no_rational_third_pure_stage
    (x:=nodes A 1/γ) (y:=nodes A 2/γ) (a:=A 2 0/γ) (b:=A 2 1/γ)
  · field_simp
    linear_combination -h₀
  · field_simp
    linear_combination h₁
  · field_simp
    linear_combination h₂
  · field_simp
    linear_combination h₃

/-- There is no unpaid but cubic-clean three-helper chart over Q.
Clock ties themselves are harmless unless the third quadratic defect
vanishes; even then an unpaid head requires genuine visible dirt. -/
theorem rational_paid_or_dirty
    {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hz : ∀ i, i∉tail → b i=0) (active : ∀ i∈tail,b i≠0)
    (inj : ∀ i j, i∈tail → j∈tail → nodes A i=nodes A j → i=j) :
    SDIRKSevenTailCubicPurity.PaidHead A ∨
      (monomialStageDefect A 1 2=0 ∧ ∃ v∈zeroSpace A 3,∃ i∈tail,v i≠0) := by
  by_cases h : monomialStageDefect A 1 2=0
  · by_cases dirty : ∃ v∈zeroSpace A 3,∃ i∈tail,v i≠0
    · exact Or.inr ⟨h,dirty⟩
    · push Not at dirty
      obtain ⟨p₀,p₁⟩ := rational_first_two_cubic_of_third_seed_zero ho ha he hγ hz active inj h
      obtain ⟨v,hv,hv₂⟩ := rational_third_cubic_nonzero ho ha he hγ
      let w := v-v 0 • Pi.single (0:F) 1-v 1 • Pi.single (1:F) 1
      have wF : w∈zeroSpace A 3 := (zeroSpace A 3).sub_mem
        ((zeroSpace A 3).sub_mem hv ((zeroSpace A 3).smul_mem _ p₀))
        ((zeroSpace A 3).smul_mem _ p₁)
      have w₂ : w 2≠0 := by
        simpa [w] using hv₂
      have s₂ : Pi.single (2:F) (1:ℚ)∈zeroSpace A 3 := by
        apply axis_from_supported wF 2 w₂
        intro j hj
        by_cases ht : j∈tail
        · have a₀ : j≠0 := fun e=>(by decide : (0:F)∉tail) (e ▸ ht)
          have a₁ : j≠1 := fun e=>(by decide : (1:F)∉tail) (e ▸ ht)
          simp [w,Pi.single_eq_of_ne a₀,Pi.single_eq_of_ne a₁,dirty v hv j ht]
        · rcases head_cases j ht with rfl | rfl | rfl
          · simp [w]
          · simp [w]
          · exact (hj rfl).elim
      left
      intro i hi
      apply zeroSpace_mono A (by decide : 3≤4)
      rcases head_cases i hi with rfl | rfl | rfl
      · exact p₀
      · exact p₁
      · exact s₂
  · exact Or.inl (rational_head_paid_of_third_seed ho ha he hγ hz active inj h)

/-- Exact rational gate: an unpaid head is equivalent to the
zero-third-seed branch with an actual visible cubic defect. -/
theorem rational_unpaid_iff_dirty
    {A : Matrix F F ℚ} {b : F→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hz : ∀ i, i∉tail → b i=0) (active : ∀ i∈tail,b i≠0)
    (inj : ∀ i j, i∈tail → j∈tail → nodes A i=nodes A j → i=j) :
    (¬SDIRKSevenTailCubicPurity.PaidHead A) ↔
      (monomialStageDefect A 1 2=0 ∧ ∃ v∈zeroSpace A 3,∃ i∈tail,v i≠0) := by
  constructor
  · intro h
    exact (rational_paid_or_dirty ho ha he hγ hz active inj).resolve_left h
  · rintro ⟨_,v,hv,i,hi,ni⟩ p
    exact ni (SDIRKSevenTailCubicPurity.tail_cubic_pure ho p ha he hγ
      (active 8 (by decide)) inj hv i hi)

end
end RKResearch.Certified.SDIRKSevenSixActive
