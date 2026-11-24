module

public import RKCert.ReviewedNative.LocalLinearSupportTools
public import RKCert.ReviewedNative.PhysicalSupportCensus

@[expose] public section

/-! Source-only draft. Literal diagonal projections retain the compensated
contrast's physical support during orthogonal removal of the early block. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint PhysicalCensus
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {U : Submodule K (Fin s→K)}

def tripleLabel (y f e : Fin s→K) (i : Fin s) : K×K×K := (y i,f i,e i)

def selectThree (y f e : Fin s→K) (a d g : K→K) (v : Fin s→K) (i : Fin s) : K :=
  a (y i)*d (f i)*g (e i)*v i

theorem selectThree_mem {y f e : Fin s→K} (hy : U.map (diag y)≤U)
    (hf : U.map (diag f)≤U) (he : U.map (diag e)≤U)
    (a d g : K→K) {v : Fin s→K} (hv : v∈U) : selectThree y f e a d g v∈U := by
  have v3 := clock_function_mem (fun _ h=>he (Submodule.mem_map_of_mem h)) g hv
  have v2 := clock_function_mem (fun _ h=>hf (Submodule.mem_map_of_mem h)) d v3
  have v1 := clock_function_mem (fun _ h=>hy (Submodule.mem_map_of_mem h)) a v2
  convert v1 using 1
  ext i
  simp only [selectThree]
  ring

theorem selectThree_annih {y f e : Fin s→K} (hy : U.map (diag y)≤U)
    (hf : U.map (diag f)≤U) (he : U.map (diag e)≤U)
    (a d g : K→K) {v : Fin s→K} (hv : v∈annih U) :
    selectThree y f e a d g v∈annih U := by
  apply mem_annih.mpr
  intro t ht
  have w := mem_annih.mp hv _ (selectThree_mem hy hf he a d g ht)
  rw [row_apply,dotProduct] at w ⊢
  convert w using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [selectThree]
  ring

/-- Every occupied joint block has a literal unit-vector mask in the
annihilator, not merely a nonzero reported weight somewhere in it. -/
theorem triple_indicator_mem_annih {y f e : Fin s→K} (hy : U.map (diag y)≤U)
    (hf : U.map (diag f)≤U) (he : U.map (diag e)≤U)
    (mass : ∀ v∈U, (∑ i,v i)=0) (x : K×K×K) :
    labelIndicator (tripleLabel y f e) x∈annih U := by
  rcases x with ⟨x₁,x₂,x₃⟩
  apply mem_annih.mpr
  intro u hu
  let a (x : K) : K := if x=x₁ then 1 else 0
  let d (x : K) : K := if x=x₂ then 1 else 0
  let g (x : K) : K := if x=x₃ then 1 else 0
  have z := mass _ (selectThree_mem hy hf he a d g hu)
  rw [row_apply,dotProduct]
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases b₁ : y i=x₁ <;> by_cases b₂ : f i=x₂ <;> by_cases b₃ : e i=x₃ <;>
    simp [labelIndicator,tripleLabel,selectThree,a,d,g,b₁,b₂,b₃]

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin s) (Fin s) K} {b τ f e : Fin s→K}
variable {h r j : ℕ} {P Q : K[X]}

set_option maxHeartbeats 850000 in
theorem local_linear_compensated_contrast (F : LocalLinearBand A b h r U τ)
    (fit : LocalLinearTraces A b U τ f r j P Q) (eK : e∈hiddenKernel b τ U)
    (binary : ∀ i,e i=0 ∨ e i=1) :
    ∃ W∈annih U,
      (∀ i,W i≠0 → e i=0 ∧ f i=0 ∧ Q.eval (reflectedClock A i)≠0) ∧
      ∃ u∈U,W=weightedEval (reflectedClock A) b Q-weightedEval (reflectedClock A) τ P-u := by
  let y := reflectedClock A
  let R := contrast y b f Q
  obtain ⟨u,hu,raw⟩ := contrast_decompose fit F.invariant
  change R=weightedEval y b Q-weightedEval y τ P-u at raw
  obtain ⟨τe,be,invE⟩ := mem_hiddenKernel.mp eK
  have ec : e*u∈U := by
    have w := invE (Submodule.mem_map_of_mem hu)
    have eq : diag e u=e*u := by ext i; simp
    exact eq ▸ w
  have eb : weightedEval y (b*e) Q∈U := reflected_clock_weighted_core F.invariant be Q
  have formula : e*R=weightedEval y (b*e) Q-e*u := by
    ext i
    rw [Pi.mul_apply,congrFun raw i]
    simp only [Pi.sub_apply,Pi.mul_apply,weightedEval_apply]
    have τei : τ i*e i=0 := congrFun τe i
    have z : e i*(P.eval (y i)*τ i)=0 := by
      rw [show e i*(P.eval (y i)*τ i)=P.eval (y i)*(τ i*e i) by ring,τei,mul_zero]
    rw [mul_sub,mul_sub,z,sub_zero]
    ring
  have removed : e*R∈U := formula.symm ▸ U.sub_mem eb ec
  let V := R-e*R
  have corrected : V=weightedEval y b Q-weightedEval y τ P-(u+e*R) := by
    change R-e*R=_
    rw [raw]
    abel
  have on (i : Fin s) (live : V i≠0) : e i=0 ∧ f i=0 ∧ Q.eval (y i)≠0 := by
    refine ⟨?_,?_,?_⟩
    · rcases binary i with zero|one
      · exact zero
      · exfalso
        exact live (by simp [V,one])
    · by_contra off
      exact live (by simp [V,R,contrast,off])
    · intro z
      exact live (by simp [V,R,contrast,z])
  let a (t : K) : K := if Q.eval t=0 then 0 else 1
  let d (t : K) : K := if t=0 then 1 else 0
  let g (t : K) : K := if t=0 then 1 else 0
  have fixed : selectThree y f e a d g V=V := by
    ext i
    by_cases z : V i=0
    · simp [selectThree,z]
    · obtain ⟨ei,fi,qi⟩ := on i z
      simp [selectThree,a,d,g,ei,fi,qi]
  have both : V∈U⊔annih U := by
    rw [dot_orthogonal_sup_top]
    exact Submodule.mem_top
  obtain ⟨w,hw,v,hv,join⟩ := Submodule.mem_sup.mp both
  let W := selectThree y f e a d g v
  let z := selectThree y f e a d g w
  have zU : z∈U := selectThree_mem F.invariant fit.preserves invE a d g hw
  have WU : W∈annih U := selectThree_annih F.invariant fit.preserves invE a d g hv
  have split : V=z+W := by
    rw [←fixed,←join]
    ext i
    simp only [z,W,selectThree,Pi.add_apply]
    ring
  have loc (i : Fin s) (nonzero : W i≠0) : e i=0 ∧ f i=0 ∧ Q.eval (y i)≠0 := by
    refine ⟨?_,?_,?_⟩
    · by_contra off
      exact nonzero (by simp [W,selectThree,g,off])
    · by_contra off
      exact nonzero (by simp [W,selectThree,d,off])
    · intro off
      exact nonzero (by simp [W,selectThree,a,off])
  refine ⟨W,WU,loc,u+e*R+z,U.add_mem (U.add_mem hu removed) zU,?_⟩
  have isol : W=V-z := by rw [split]; abel
  rw [isol,corrected]
  abel

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
