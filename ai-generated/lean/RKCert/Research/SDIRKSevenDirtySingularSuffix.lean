module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Two singular reflected suffixes are impossible
Only the first two reverse reads, the second-error row's action,
and three paid moment tests are needed. The hypotheses are the
normalized dirty-tail reverse interface, not a solver ansatz. -/
namespace RKResearch.Certified.SDIRKSevenDirtySingularSuffix
open scoped Matrix BigOperators Classical
noncomputable section
abbrev F := Fin 6
variable {K : Type*} [Field K]

private theorem row_at {B : Matrix F F K} (ha : B.IsLowerTriangular)
    (he : ∀ i, B i i=1) {v : F→K} (i : F) (zero : ∀ j, i<j → v j=0) :
    (v ᵥ* B) i=v i := by
  change (∑ j, v j*B j i)=v i
  rw [Finset.sum_eq_single i,he i,mul_one]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · have e : B j i=0 := @ha j i h
      rw [e,mul_zero]
    · rw [zero j h,zero_mul]
  · simp

private theorem last {B : Matrix F F K} (ha : B.IsLowerTriangular)
    (he : ∀ i,B i i=1) (v : F→K) : (v ᵥ* B) 5=v 5 := by
  apply row_at ha he
  intro j hj
  have h : 5<j.val := hj
  omega

private theorem penult {B : Matrix F F K} (ha : B.IsLowerTriangular)
    (he : ∀ i,B i i=1) (v : F→K) : (v ᵥ* B) 4=v 4+v 5*B 5 4 := by
  change (∑ j,v j*B j 4) = _
  have hsum : (∑ j ∈ ({4,5}:Finset F),v j*B j 4)=(∑ j,v j*B j 4) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have n₄ : j≠4 := by intro e; exact hj (by simp [e])
    have n₅ : j≠5 := by intro e; exact hj (by simp [e])
    have e₄ : j.val≠4 := fun e=>n₄ (Fin.ext e)
    have e₅ : j.val≠5 := fun e=>n₅ (Fin.ext e)
    have h : j< (4:F) := by change j.val<4; omega
    have h' : B j 4=0 := @ha j (4:F) h
    rw [h',mul_zero]
  rw [←hsum,Finset.sum_pair (by decide : (4:F)≠5),he 4,mul_one]

private theorem eigen_zero {B : Matrix F F K} (ha : B.IsLowerTriangular)
    (he : ∀ i,B i i=1) {v y : F→K}
    (ev : ∀ i,(v ᵥ* B) i=v i*y i)
    (cut : ∀ i,y i=1 → v i=0) : ∀ i,v i=0 := by
  classical
  intro j
  by_contra hn
  let S := Finset.univ.filter (fun i => v i≠0)
  let pivot := S.max' ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  have hp : pivot∈S := Finset.max'_mem _ _
  have pu : v pivot≠0 := (Finset.mem_filter.mp hp).2
  have zero (t : F) (lt : pivot<t) : v t=0 := by
    by_contra nn
    have hh : t∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,nn⟩
    exact (not_le_of_gt lt) (Finset.le_max' _ _ hh)
  have e := ev pivot
  rw [row_at ha he pivot zero] at e
  have e' : v pivot*(y pivot-1)=0 := by linear_combination -e
  have yp : y pivot=1 := sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_left pu)
  exact pu (cut pivot yp)

private theorem mix_row (B : Matrix F F K) (v w : F→K) (i : F) :
    ((fun j=>v j+w j/2) ᵥ* B) i=(v ᵥ* B) i+(w ᵥ* B) i/2 := by
  change (∑ j,(v j+w j/2)*B j i)=(∑ j,v j*B j i)+(∑ j,w j*B j i)/2
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable [CharZero K]

private theorem terminal_errors {B : Matrix F F K} {b y D : F→K}
    (ha : B.IsLowerTriangular) (he : ∀ i,B i i=1) (finish : y 5=1)
    (first : ∀ i,(b ᵥ* B) i=b i*y i)
    (second : ∀ i,((fun j=>b j*y j) ᵥ* B) i=b i*(y i)^2/2-D i) :
    D 5= -b 5/2 ∧ D 4=b 4*((y 4)^2/2-2*y 4+1) := by
  have d5 := second 5
  rw [last ha he,finish] at d5
  have t := first 4
  rw [penult ha he] at t
  have p := second 4
  rw [penult ha he,finish] at p
  simp only [mul_one] at p
  constructor
  · linear_combination d5
  · linear_combination p-t

private theorem moment_payment {b y D : F→K} {z h δ : K} {e k : ℕ}
    (law : ∀ i,D i=-(b i*(y i)^e)/2)
    (mom : ∀ i : ℕ, i≤3 →(∑ j,b j*(y j)^i)=z^i/((i:K)+1))
    (dmom : ∀ i≤2,δ*h^i+(∑ j,D j*(y j)^i)=0)
    (hk : k≤2) (he : e+k≤3) :
    δ*h^k=(z^(e+k)/(((e+k:ℕ):K)+1))/2 := by
  have hm := dmom k hk
  have t : (∑ j,D j*(y j)^k)=-(∑ j,b j*(y j)^(e+k))/2 := by
    simp only [div_eq_mul_inv]
    rw [←Finset.sum_neg_distrib,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [law j,pow_add]
    ring
  rw [t,mom (e+k) he] at hm
  linear_combination hm

private theorem no_moment_linear {b y D : F→K} {z h δ : K} (hz : z≠0)
    (law : ∀ i,D i=-(b i*y i)/2)
    (mom : ∀ i : ℕ, i≤3 →(∑ j,b j*(y j)^i)=z^i/((i:K)+1))
    (dmom : ∀ i≤2,δ*h^i+(∑ j,D j*(y j)^i)=0) : False := by
  have hl (i : F) : D i=-(b i*(y i)^1)/2 := by simpa only [pow_one] using law i
  have e₀ := moment_payment hl mom dmom (k:=0) (by decide) (by decide)
  have e₁ := moment_payment hl mom dmom (k:=1) (by decide) (by decide)
  have e₂ := moment_payment hl mom dmom (k:=2) (by decide) (by decide)
  norm_num at e₀ e₁ e₂
  have dd : δ=z/4 := by linear_combination e₀
  rw [dd] at e₁ e₂
  have he : z*(3*h-2*z)=0 := by linear_combination 12*e₁
  have hh : h=2*z/3 := by
    have z' := (mul_eq_zero.mp he).resolve_left hz
    linear_combination z'/3
  rw [hh] at e₂
  have z0 : z^3=0 := by linear_combination -72*e₂
  exact pow_ne_zero 3 hz z0

private theorem no_moment_constant {b y D : F→K} {z h δ : K} (hz : z≠0)
    (law : ∀ i,D i= -b i/2)
    (mom : ∀ i : ℕ, i≤3 →(∑ j,b j*(y j)^i)=z^i/((i:K)+1))
    (dmom : ∀ i≤2,δ*h^i+(∑ j,D j*(y j)^i)=0) : False := by
  have hl (i : F) : D i=-(b i*(y i)^0)/2 := by simpa only [pow_zero,mul_one] using law i
  have e₀ := moment_payment hl mom dmom (k:=0) (by decide) (by decide)
  have e₁ := moment_payment hl mom dmom (k:=1) (by decide) (by decide)
  have e₂ := moment_payment hl mom dmom (k:=2) (by decide) (by decide)
  norm_num at e₀ e₁ e₂
  rw [e₀] at e₁ e₂
  have hh : h=z/2 := by linear_combination 2*e₁
  rw [hh] at e₂
  have z0 : z^2=0 := by linear_combination -24*e₂
  exact pow_ne_zero 2 hz z0

/-- In the actual dirty reverse interface, a penultimate normalized
reflected clock of two or three is impossible, even with a tied ghost
clock and without any assumptions on signs or the third reverse row. -/
theorem no_two_or_three {B : Matrix F F K} {b y D : F→K} {z h δ : K}
    (ha : B.IsLowerTriangular) (he : ∀ i,B i i=1)
    (hz : z≠0) (inj : Function.Injective y) (finish : y 5=1)
    (first : ∀ i,(b ᵥ* B) i=b i*y i)
    (second : ∀ i,((fun j=>b j*y j) ᵥ* B) i=b i*(y i)^2/2-D i)
    (reverse : ∀ i,(D ᵥ* B) i=D i*(1+(1-y i)/((y 4)^2-4*y 4+2)))
    (mom : ∀ i : ℕ, i≤3 →(∑ j,b j*(y j)^i)=z^i/((i:K)+1))
    (dmom : ∀ i≤2,δ*h^i+(∑ j,D j*(y j)^i)=0) :
    y 4≠2 ∧ y 4≠3 := by
  have err := terminal_errors ha he finish first second
  constructor
  · intro u
    let E := fun i => D i+(b i*y i)/2
    have ea (i : F) : (E ᵥ* B) i=E i*(y i/2) := by
      change ((fun j=>D j+(b j*y j)/2) ᵥ* B) i=_
      rw [mix_row,second i,reverse i,u]
      dsimp [E]
      ring
    have zn (i : F) (e : y i/2=1) : E i=0 := by
      have d : y i=2 := by linear_combination 2*e
      have q : i=4 := inj (d.trans u.symm)
      subst i
      change D 4+b 4*y 4/2=0
      rw [err.2,u]
      ring
    have e := eigen_zero ha he ea zn
    apply no_moment_linear hz (D:=D) ?_ mom dmom
    intro i
    have l := e i
    change D i+b i*y i/2=0 at l
    linear_combination l
  · intro u
    let E := fun i=>D i+b i/2
    have ea (i : F) : (E ᵥ* B) i=E i*y i := by
      change ((fun j=>D j+(b j)/2) ᵥ* B) i=_
      rw [mix_row,first i,reverse i,u]
      dsimp [E]
      ring
    have zn (i : F) (e : y i=1) : E i=0 := by
      have q : i=5 := inj (e.trans finish.symm)
      subst i
      change D 5+b 5/2=0
      linear_combination err.1
    have e := eigen_zero ha he ea zn
    apply no_moment_constant hz (D:=D) ?_ mom dmom
    intro i
    have l := e i
    change D i+b i/2=0 at l
    linear_combination l

end
end RKResearch.Certified.SDIRKSevenDirtySingularSuffix
