module

public import RKCert.GradedProducts

@[expose] public section

/-! # The primitive and commutator as actual homogeneous tree defects

The commutator is not merely invisible to some probes: its value on every
grade-`j` tree column belongs to the actual homogeneous defect span at
grade `j+2`. Multiplication by the two small integers required for the
identity is inverted only because the order equations already make them units.
-/
namespace RKCert.Paired

variable {R : Type*} [CommRing R] {s p : ℕ} {A : Fin s → Fin s → R} {b : Vec R s}

/-- Every normalized bush primitive defect is in the proper homogeneous grade. -/
theorem primitive_mem_zeroSpace (A : Fin s → Fin s → R) (n : ℕ) :
    ((n+1 : ℕ):R) • mat A (fun i => nodes A i ^ n) - (fun i => nodes A i ^ (n+1)) ∈
      zeroSpace A (n+1) := by
  have h := normDiff_mem (n:=n+1) A ((Tree.bush n).attach .leaf) (Tree.bush (n+1))
    (by simp only [Tree.order,Tree.order_bush]) (by simp only [Tree.order,Tree.order_bush]; omega)
  rwa [normTree_unary, Tree.order_bush, normTree_bush, normTree_bush] at h

/-- Exact forward operator identity over rings, with no triangularity.
The displayed map is definitionally the commutator used in the nonsingular
DIRK rank argument over fields. -/
theorem commutator_mem_zeroSpace (ho : HasTreeOrderAtLeast A b p) (j : ℕ) (hj : j+2≤p) :
    treeSpace A j ≤ (zeroSpace A (j+2)).comap
      ((diag (nodes A)).comp (mat A) - (mat A).comp (diag (nodes A)) -
        (mat A).comp (mat A)) := by
  let C := diag (nodes A)
  let B := mat A
  let T := C.comp B - B.comp C - B.comp B
  change treeSpace A j ≤ (zeroSpace A (j+2)).comap T
  apply Submodule.span_le.mpr
  rintro _ ⟨t,ht,rfl⟩
  change T (stageWeight A t) ∈ zeroSpace A (j+2)
  let u := t.attach .leaf
  let v := Tree.leaf.attach t
  let a := Tree.leaf.attach u
  let e := v.attach .leaf
  let f := u.attach .leaf
  have horders : a.order = t.order+2 ∧ e.order=t.order+2 ∧ f.order=t.order+2 := by
    dsimp [a,e,f,u,v,Tree.order]; omega
  have h1 := normDiff_mem (n:=j+2) A a e (by omega) (by omega)
  have h2 := normDiff_mem (n:=j+2) A a f (by omega) (by omega)
  have hcombo := (zeroSpace A (j+2)).add_mem ((zeroSpace A (j+2)).smul_mem (t.order:R) h1) h2
  have eqn : (t.order:R) • (normTree A a-normTree A e) + (normTree A a-normTree A f) =
      ((t.order:R) * ((t.order:R)+1)) • T (normTree A t) := by
    dsimp only [a,e,f,u,v,T,C,B]
    simp only [normTree_shift, normTree_unary, Tree.order, Nat.cast_add, Nat.cast_one,
      map_smul, LinearMap.sub_apply, LinearMap.comp_apply, smul_smul]
    ext i
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [eqn] at hcombo
  have hnat := isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) t.order_pos (by omega)
  have hnext := isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho)
    (by omega : 0<t.order+1) (by omega)
  rw [Nat.cast_add, Nat.cast_one] at hnext
  have hnorm := ((zeroSpace A (j+2)).smul_mem_iff_of_isUnit (hnat.mul hnext)).mp hcombo
  have hden := treeDensity_isUnit_of_moments (hasMomentsThrough_of_treeOrder ho) t (by omega)
  rw [Tree.density, Nat.cast_mul] at hden
  rw [normTree, map_smul] at hnorm
  exact ((zeroSpace A (j+2)).smul_mem_iff_of_isUnit (isUnit_of_mul_isUnit_right hden)).mp hnorm

end RKCert.Paired
