module

public import RKCert.Research.SDIRKSevenTailCollisionMoments
public import RKCert.ReviewedNative.GradedProducts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Any quadratic defect vanishes on the six distinct weighted nodes

This uses the square of a grade-two defect, not positivity of the weights
or any assumption about the clocks of the three zero-weight stages. -/
namespace RKResearch.Certified.SDIRKSevenSixActive
open RKResearch Graded SDIRKSevenTailCollision
open scoped Matrix BigOperators Classical

noncomputable section
variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]

omit [CharZero K] in
theorem supported_moments_zero {c w : ι → K} (S : Finset ι)
    (injective : ∀ i j, i ∈ S → j ∈ S → c i=c j → i=j)
    (supp : ∀ i, i∉S → w i=0) {n : ℕ} (size : S.card ≤ n+1)
    (moment : ∀ j≤n, (∑ i,w i*(c i)^j)=0) (a : ι) (ha : a∈S) :
    w a = 0 := by
  classical
  let sites := S.image c
  have sz : sites.card ≤ n+1 := Finset.card_image_le.trans size
  have covers (i : ι) (hi : w i≠0) : c i ∈ sites := by
    have m : i∈S := by by_contra z; exact hi (supp i z)
    exact Finset.mem_image.mpr ⟨i,m,rfl⟩
  have h := fiber_zero moment sites sz covers (c a)
  have e : (∑ i ∈ ({a}:Finset ι),w i) =
      (∑ i ∈ Finset.univ.filter (fun i => c i=c a),w i) := by
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      have eq := Finset.mem_singleton.mp hi
      simp [eq]
    · intro i hi hi'
      by_cases hs : i ∈ S
      · have eq : c i=c a := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
        exact (hi' (Finset.mem_singleton.mpr (injective _ _ hs ha eq))).elim
      · exact supp i hs
  simpa only [Finset.sum_singleton] using e.trans h

omit [Fintype ι] [CharZero K] in
private theorem interpolate3
    {x₀ x₁ x₂ v₀ v₁ v₂ : K} (h₀₁ : x₀≠x₁) (h₀₂ : x₀≠x₂) (h₁₂ : x₁≠x₂) :
    ∃ a b d, a+b*x₀+d*x₀^2=v₀ ∧ a+b*x₁+d*x₁^2=v₁ ∧ a+b*x₂+d*x₂^2=v₂ := by
  let u₀ := v₀/((x₀-x₁)*(x₀-x₂))
  let u₁ := v₁/((x₁-x₀)*(x₁-x₂))
  let u₂ := v₂/((x₂-x₀)*(x₂-x₁))
  have e₀ : u₀*((x₀-x₁)*(x₀-x₂))=v₀ := div_mul_cancel₀ _ (mul_ne_zero
    (sub_ne_zero.mpr h₀₁) (sub_ne_zero.mpr h₀₂))
  have e₁ : u₁*((x₁-x₀)*(x₁-x₂))=v₁ := div_mul_cancel₀ _ (mul_ne_zero
    (sub_ne_zero.mpr h₀₁.symm) (sub_ne_zero.mpr h₁₂))
  have e₂ : u₂*((x₂-x₀)*(x₂-x₁))=v₂ := div_mul_cancel₀ _ (mul_ne_zero
    (sub_ne_zero.mpr h₀₂.symm) (sub_ne_zero.mpr h₁₂.symm))
  refine ⟨u₀*x₁*x₂+u₁*x₀*x₂+u₂*x₀*x₁,-u₀*(x₁+x₂)-u₁*(x₀+x₂)-u₂*(x₀+x₁),u₀+u₁+u₂,?_,?_,?_⟩
  · linear_combination e₀
  · linear_combination e₁
  · linear_combination e₂

omit [CharZero K] in
private theorem quadratic_expand (u c : ι → K) (a b d : K) (j : ℕ) :
    (∑ i, u i * c i ^ j * (a+b*c i+d*c i^2)) =
      a*(∑ i, u i*c i^j)+b*(∑ i, u i*c i^(j+1))+d*(∑ i,u i*c i^(j+2)) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_add,pow_one]
  ring

omit [CharZero K] in
private theorem defect_moment {A : Matrix ι ι K} {b v : ι → K} {q j : ℕ}
    (ho : HasOrder 7 A b) (hv : v∈zeroSpace A q) (budget : j+q+1≤7) :
    (∑ i,b i*(nodes A i)^j*v i)=0 :=
  LinearMap.mem_ker.mp (probe_zeroSpace ho budget hv)

/-- With exactly six active stages at distinct physical clocks, every
grade-two homogeneous defect is hidden at order seven. There is no
triangularity, common diagonal, or ordered-field hypothesis. -/
theorem quadratic_hidden {A : Matrix ι ι K} {b v : ι → K}
    (ho : HasOrder 7 A b) (S : Finset ι) (card : S.card=6)
    (head : ∀ i, i∉S → b i=0) (active : ∀ i∈S,b i≠0)
    (inj : ∀ i j, i∈S → j∈S → nodes A i=nodes A j → i=j)
    (hv : v∈zeroSpace A 2) : ∀ i∈S,v i=0 := by
  classical
  let c := nodes A
  let w := fun i => b i*v i
  have hw (j : ℕ) (hj : j≤4) : (∑ i,w i*c i^j)=0 := by
    have h := defect_moment ho hv (j:=j) (by omega)
    simpa only [w,c,mul_right_comm] using h
  have weighted_square (j : ℕ) (hj : j≤2) : (∑ i,w i*c i^j*v i)=0 := by
    have h := defect_moment ho (zeroSpace_mul hv hv) (j:=j) (by omega)
    simp only [Pi.mul_apply] at h
    simpa only [w,c,mul_right_comm,mul_assoc] using h
  have ws (i : ι) (hi : i∉S) : w i=0 := by simp [w,head i hi]
  intro k hk
  by_contra hnk
  have wk : w k≠0 := mul_ne_zero (active k hk) hnk
  have well (i : ι) (hi : i∈S) : w i≠0 := by
    intro hi'
    have ka : k∈S.erase i := by
      apply Finset.mem_erase.mpr
      exact ⟨fun e => wk (e ▸ hi'),hk⟩
    apply wk
    exact supported_moments_zero (S.erase i)
      (fun x y hx hy e => inj x y (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) e)
      (fun j hj => by
        by_cases ji : j=i
        · simpa [ji] using hi'
        · exact ws j (fun hh => hj (Finset.mem_erase.mpr ⟨ji,hh⟩)))
        (by rw [Finset.card_erase_of_mem hi,card]) hw k ka
  obtain ⟨i₀,hi₀⟩ := Finset.card_pos.mp (by omega : 0<S.card)
  have c₁ : (S.erase i₀).card=5 := by simp [Finset.card_erase_of_mem hi₀,card]
  obtain ⟨i₁,hi₁⟩ := Finset.card_pos.mp (by omega : 0<(S.erase i₀).card)
  have c₂ : ((S.erase i₀).erase i₁).card=4 := by simp [Finset.card_erase_of_mem hi₁,c₁]
  obtain ⟨i₂,hi₂⟩ := Finset.card_pos.mp (by omega : 0<((S.erase i₀).erase i₁).card)
  have hi₁S := Finset.mem_of_mem_erase hi₁
  have hi₂S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi₂)
  obtain ⟨a₀,a₁,a₂,Q₀,Q₁,Q₂⟩ := interpolate3 (v₀:=v i₀) (v₁:=v i₁) (v₂:=v i₂)
    (fun e => (Finset.ne_of_mem_erase hi₁) (inj _ _ hi₀ hi₁S e).symm)
    (fun e => (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi₂)) (inj _ _ hi₀ hi₂S e).symm)
    (fun e => (Finset.ne_of_mem_erase hi₂) (inj _ _ hi₁S hi₂S e).symm)
  let P := fun i => a₀+a₁*c i+a₂*c i^2
  let X := ((S.erase i₀).erase i₁).erase i₂
  let d := fun i => w i*(v i-P i)
  have ss (i : ι) (hi : i∉X) : d i=0 := by
    by_cases hs : i∈S
    · have e : i=i₀ ∨ i=i₁ ∨ i=i₂ := by
        by_contra h
        push Not at h
        exact hi (by simp [X,hs,h])
      rcases e with rfl | rfl | rfl
      · simp [d,P,c,Q₀]
      · simp [d,P,c,Q₁]
      · simp [d,P,c,Q₂]
    · simp [d,ws i hs]
  have dd (j : ℕ) (hj : j≤2) : (∑ i,d i*c i^j)=0 := by
    have hp : (∑ i,w i*c i^j * P i)=0 := by
      change (∑ i,w i*c i^j*(a₀+a₁*c i+a₂*c i^2))=0
      rw [quadratic_expand,hw j (by omega),hw (j+1) (by omega),hw (j+2) (by omega)]
      ring
    calc
      _ = (∑ i,w i*c i^j*v i) - (∑ i,w i*c i^j*P i) := by
        rw [←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _; dsimp [d]; ring
      _ = 0 := by rw [hp,weighted_square j hj,sub_self]
  have agree (i : ι) (hi : i∈S) : v i=P i := by
    have ee : d i=0 := by
      by_cases hh : i ∈ X
      · apply supported_moments_zero X
          (fun x y hx hy e => inj _ _ (by simpa [X] using And.right (And.right (And.right
            (show (x ≠ i₂ ∧ x ≠ i₁ ∧ x ≠ i₀ ∧ x ∈ S) by simpa [X] using hx))))
            (by simpa [X] using And.right (And.right (And.right
            (show (y ≠ i₂ ∧ y ≠ i₁ ∧ y ≠ i₀ ∧ y ∈ S) by simpa [X] using hy)))) e) ss ?_ dd i hh
        rw [show X.card=3 by simp [X,Finset.card_erase_of_mem hi₂,c₂]]
      · exact ss i hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp ee).resolve_left (well i hi))
  have L (j : ℕ) (hj : j≤2) :
      a₀/((j:K)+1)+a₁/((j:K)+2)+a₂/((j:K)+3)=0 := by
    have h := defect_moment ho hv (j:=j) (by omega)
    have e : (∑ i,b i*c i^j*P i)=0 := by
      rw [←h]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈S
      · rw [agree i hi]
      · simp [head i hi]
    change (∑ i,b i*c i^j*(a₀+a₁*c i+a₂*c i^2))=0 at e
    rw [quadratic_expand,clock_moment ho j (by omega),clock_moment ho (j+1) (by omega),
      clock_moment ho (j+2) (by omega)] at e
    simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at e
    rw [show (j:K)+1+1=(j:K)+2 by ring,show (j:K)+2+1=(j:K)+3 by ring] at e
    simpa only [div_eq_mul_inv,one_mul] using e
  have L₀ := L 0 (by decide)
  have L₁ := L 1 (by decide)
  have L₂ := L 2 (by decide)
  norm_num at L₀ L₁ L₂
  have a : a₀=0 := by linear_combination 9*L₀-36*L₁+30*L₂
  have b : a₁=0 := by linear_combination -36*L₀+192*L₁-180*L₂
  have d₀ : a₂=0 := by linear_combination 30*L₀-180*L₁+180*L₂
  exact hnk (by rw [agree k hk]; simp [P,a,b,d₀])

end
end RKResearch.Certified.SDIRKSevenSixActive
