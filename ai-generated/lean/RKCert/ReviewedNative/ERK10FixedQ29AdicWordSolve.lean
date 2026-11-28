module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordPivots

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Matrix
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

def leadingLength (i : Site) : ℕ := min i.val 8
theorem leading_le (i : Site) : leadingLength i ≤ 8 := Nat.min_le_right _ _
theorem leading_le_row (i : Site) : leadingLength i ≤ i.val := Nat.min_le_left _ _
theorem leading_le_sites (i : Site) : leadingLength i ≤ 11 := (leading_le i).trans (by decide)

def extendLeading {m : ℕ} (v : Fin m→R) (j : Site) : R :=
  if hj : j.val<m then v ⟨j.val,hj⟩ else 0

theorem sum_extendLeading {m : ℕ} (hm : m≤11) (v : Fin m→R) (g : Site→R) :
    ∑ j : Site, extendLeading v j*g j =
      ∑ k : Fin m, v k*g (Fin.castLE hm k) := by
  let S : Finset Site := Finset.univ.filter (fun j : Site => j.val<m)
  have hS : (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hm)=S := by
    ext j
    rw [Finset.mem_map,Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Fin.castLEEmb_apply]
    constructor
    · rintro ⟨k,rfl⟩
      exact k.isLt
    · intro hj
      exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩
  have hSum : (∑ j : Site, extendLeading v j*g j)=∑ j∈S,extendLeading v j*g j := by
    unfold S
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<m
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj,extendLeading,dite_eq_right hj,zero_mul]
  rw [hSum,←hS,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (Fin.castLE hm k).val<m := k.isLt
  change extendLeading v (Fin.castLE hm k)*g (Fin.castLE hm k)=_
  rw [extendLeading,dite_eq_left hk]
  rfl

/-- The three fixed free taps in strict reverse chronology. -/
def HostInput.chronologicalPorts (p : HostInput R) (i j : Site) : R :=
  if i=9 ∧ j=8 then p.zb else
  if i=10 ∧ j=8 then p.za else
  if i=10 ∧ j=9 then p.va else 0

theorem chronological_ports_strict (p : HostInput R) : strictlyLower p.chronologicalPorts := by
  intro i j hij
  unfold HostInput.chronologicalPorts
  split
  · rename_i h
    obtain ⟨rfl,rfl⟩ := h
    exact ((show ¬ ((9:Site) ≤ (8:Site)) from by decide +kernel) hij).elim
  · split
    · rename_i h
      obtain ⟨rfl,rfl⟩ := h
      exact ((show ¬ ((10:Site) ≤ (8:Site)) from by decide +kernel) hij).elim
    · split
      · rename_i h
        obtain ⟨rfl,rfl⟩ := h
        exact ((show ¬ ((10:Site) ≤ (9:Site)) from by decide +kernel) hij).elim
      · rfl

def rowRight (A T : Site→Word→R) (D : Site→Site→R) (i : Site) (j : Word) : R :=
  T i j-∑ k : Site,D i k*A k j

def rowCoeffs (A T : Site→Word→R) (D : Site→Site→R) (i : Site) :
    Fin (leadingLength i)→R :=
  (fun j => rowRight A T D i (Fin.castLE (leading_le i) j)) ᵥ*
      (leadWords A (leadingLength i) (leading_le i))⁻¹

def chronologicalK (A T : Site→Word→R) (D : Site→Site→R) : Site→Site→R :=
  fun i j => extendLeading (rowCoeffs A T D i) j+D i j

theorem chronologicalK_strict (A T : Site→Word→R) {D : Site→Site→R} (hD : strictlyLower D) :
    strictlyLower (chronologicalK A T D) := by
  intro i j hij
  have hh : ¬ j.val<leadingLength i := by
    have h := leading_le_row i
    change i.val≤j.val at hij
    omega
  rw [chronologicalK,extendLeading,dite_eq_right hh,zero_add,hD _ _ hij]

/-- The exact row coefficients on each chronological leading square cut,
over an arbitrary ring when its determinant is a unit. -/
theorem chronologicalK_selected (A T : Site→Word→R) (D : Site→Site→R) (i : Site)
    (hu : IsUnit (leadWords A (leadingLength i) (leading_le i)).det)
    (k : Fin (leadingLength i)) :
    ∑ j : Site, chronologicalK A T D i j*A j (Fin.castLE (leading_le i) k) =
      T i (Fin.castLE (leading_le i) k) := by
  let M := leadWords A (leadingLength i) (leading_le i)
  let v : Fin (leadingLength i)→R := fun j => rowRight A T D i (Fin.castLE (leading_le i) j)
  have hs : rowCoeffs A T D i ᵥ* M=v := by
    change (v ᵥ* M⁻¹) ᵥ* M=v
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul _ hu,Matrix.vecMul_one]
  have h := congrFun hs k
  change (∑ j : Fin (leadingLength i), rowCoeffs A T D i j*
    A (Fin.castLE (leading_le_sites i) j) (Fin.castLE (leading_le i) k)) = _ at h
  simp only [chronologicalK,add_mul,Finset.sum_add_distrib,
    sum_extendLeading (leading_le_sites i)]
  rw [h]
  simp [v,rowRight,sub_add_cancel]

theorem chronologicalK_late (A T : Site→Word→R) (D : Site→Site→R) (i : Site)
    (hi : 8 ≤ i.val) (hu : IsUnit (leadWords A (leadingLength i) (leading_le i)).det)
    (k : Word) :
    ∑ j : Site, chronologicalK A T D i j*A j k=T i k := by
  have hlen : leadingLength i=8 := Nat.min_eq_right hi
  let ko : Fin (leadingLength i) := ⟨k.val,by simpa only [hlen] using k.isLt⟩
  have hk : Fin.castLE (leading_le i) ko=k := Fin.ext rfl
  simpa only [hk] using chronologicalK_selected A T D i hu ko

theorem chronologicalK_actualPorts (A T : Site→Word→R) (p : HostInput R) :
    chronologicalK A T p.chronologicalPorts 9 8=p.zb ∧
    chronologicalK A T p.chronologicalPorts 10 8=p.za ∧
    chronologicalK A T p.chronologicalPorts 10 9=p.va := by
  simp [chronologicalK,extendLeading,HostInput.chronologicalPorts,leadingLength]

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.chronologicalK_strict
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.chronologicalK_selected
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.chronologicalK_late
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.chronologicalK_actualPorts
