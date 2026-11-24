module

public import RKCert.ReviewedNative.LocalLinearTraces

@[expose] public section

/-! The first failing reverse prefix can be tested on its *joint*
numerical clock and feature block. No individual weight is inverted. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}

theorem reverse_first_unmatched_joint (y f v : Fin s→K)
    (U : Submodule K (Fin s→K)) (stableY : MaskInvariant y U)
    (stableF : MaskInvariant f U) (out : v∉U) :
    ∃ i : Fin s, ∃ w∈U, (∀ j > i, w j=v j) ∧
      ¬∃ z∈U, ∀ j : Fin s, i≤j → y j=y i → f j=f i → z j=v j := by
  let M (n : ℕ) := ∃ u∈U, ∀ j : Fin s,(Fin.rev j).val<n → u j=v j
  have ex : ∃ n, ¬M n := by
    refine ⟨s,fun ⟨u,hu,e⟩=>out ?_⟩
    have h : u=v := funext fun j => e j (Fin.rev j).isLt
    rwa [h] at hu
  let n := Nat.find ex
  have fail : ¬M n := Nat.find_spec ex
  have legal : n≤s := Nat.find_min' ex (by
    rintro ⟨u,hu,e⟩
    have h : u=v := funext fun j=>e j (Fin.rev j).isLt
    exact out (h ▸ hu))
  have pos : 0<n := by
    by_contra! small
    have z : n=0 := by omega
    exact fail ⟨0,U.zero_mem,fun j h=>by rw [z] at h; omega⟩
  let k : Fin s := ⟨n-1,by omega⟩
  let i : Fin s := Fin.rev k
  have ri : (Fin.rev i).val+1=n := by
    simp only [i,Fin.rev_rev,k]
    omega
  obtain ⟨w,hw,earlier⟩ := (not_not.mp (Nat.find_min ex
    (by omega : (Fin.rev i).val<n)) : M (Fin.rev i).val)
  refine ⟨i,w,hw,fun j h=>earlier j (Fin.rev_lt_rev.mpr h),?_⟩
  rintro ⟨z,hz,same⟩
  let w' := w+blockMask y (y i) (blockMask f (f i) (z-w))
  refine fail ⟨w',U.add_mem hw (stableY _ _ (stableF _ _ (U.sub_mem hz hw))),?_⟩
  intro j hj
  have le : i≤j := Fin.rev_le_rev.mp (by change (Fin.rev j).val ≤ (Fin.rev i).val; omega)
  by_cases sy : y j=y i
  · by_cases sf : f j=f i
    · have eq := same j le sy sf
      simp [w',blockMask,sy,sf,eq]
    · have prev : i<j := lt_of_le_of_ne le (fun h=>sf (congrArg f h.symm))
      simp [w',blockMask,sy,sf,earlier j (Fin.rev_lt_rev.mpr prev)]
  · have prev : i<j := lt_of_le_of_ne le (fun h=>sy (congrArg y h.symm))
    simp [w',blockMask,sy,earlier j (Fin.rev_lt_rev.mpr prev)]

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
