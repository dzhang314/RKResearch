module
public import RKCert.ReviewedNative.GradedDefects
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-! # Native triangular prefix restriction and exact physical receiver order -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

section Semiring
variable {R : Type*} [CommSemiring R] {s k:ℕ}

/-- The actual leading submatrix, including an empty prefix if needed. -/
abbrev prefixMatrix (A:Matrix (Fin s) (Fin s) R) (hk:k≤s) : Matrix (Fin k) (Fin k) R :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

abbrev prefixRestrict (hk:k≤s) : (Fin s→R) →ₗ[R] (Fin k→R) :=
  LinearMap.funLeft R R (Fin.castLE hk)

@[simp] theorem prefixRestrict_apply (hk:k≤s) (v:Fin s→R) (i:Fin k) :
    prefixRestrict hk v i=v (Fin.castLE hk i) := rfl

theorem sum_prefix_zero_tail (hk:k≤s) (v:Fin s→R) (hz:∀j,k≤j.val→v j=0) :
    (∑ j:Fin k,v (Fin.castLE hk j))=∑ j:Fin s,v j := by
  classical
  have S : Finset.map (Fin.castLEEmb hk) Finset.univ=
      Finset.univ.filter (fun j:Fin s=>j.val<k) := by
    ext j
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨l,rfl⟩; exact l.isLt
    · intro hj;exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩
  change (∑ j∈Finset.univ,v (Fin.castLEEmb hk j))=_
  rw [←Finset.sum_map,S,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h:j.val<k
  · simp [h]
  · simp [h,hz j (by omega)]

theorem prefix_strict_lower {A:Matrix (Fin s) (Fin s) R}
    (strict:∀i j,i≤j→A i j=0) (hk:k≤s) :
    ∀i j:Fin k,i≤j→(prefixMatrix A hk) i j=0 :=
  fun i j h=>strict (Fin.castLE hk i) (Fin.castLE hk j) h

theorem prefix_mulVec {A:Matrix (Fin s) (Fin s) R}
    (strict:∀i j,i≤j→A i j=0) (hk:k≤s) (v:Fin s→R) :
    prefixMatrix A hk *ᵥ prefixRestrict hk v=prefixRestrict hk (A *ᵥ v) := by
  ext i
  exact sum_prefix_zero_tail hk (fun j=>A (Fin.castLE hk i) j*v j)
    (fun j hj => by rw [strict _ _ (by change i.val≤j.val; have :=i.isLt; omega),zero_mul])

theorem Φ_prefix {A:Matrix (Fin s) (Fin s) R}
    (strict:∀i j,i≤j→A i j=0) (hk:k≤s) (t:FiniteRootedTree) :
    Φ t (prefixMatrix A hk)=prefixRestrict hk (Φ t A) := by
  induction t with
  | leaf => rfl
  | butcherProduct t b ihT ihB =>
    rw [Φ,Φ,ihT,ihB,prefix_mulVec strict hk]
    rfl

theorem normTree_prefix {A:Matrix (Fin s) (Fin s) R}
    (strict:∀i j,i≤j→A i j=0) (hk:k≤s) (t:FiniteRootedTree) :
    normTree (prefixMatrix A hk) t=prefixRestrict hk (normTree A t) := by
  rw [normTree,Φ_prefix strict hk,normTree,map_smul]

theorem Φ_smul {ι : Type*} [Fintype ι] (a:R) (A:Matrix ι ι R) (t:FiniteRootedTree) :
    Φ t (a•A)=a^((t.order:ℕ)-1) • Φ t A := by
  induction t with
  | leaf => simp
  | butcherProduct t b ihT ihB =>
    have ht := t.order.pos
    have hb := b.order.pos
    have p : (((t ◂ b).order):ℕ)-1=((t.order:ℕ)-1)+(1+((b.order:ℕ)-1)) := by
      simp only [order,PNat.add_coe];omega
    rw [Φ,Φ,ihT,ihB,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,p,pow_add,pow_add,pow_one]
    ext i
    simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul]
    ac_rfl

end Semiring

section Ring
variable {R : Type*} [CommRing R] {s k:ℕ}

theorem zeroSpace_prefix {A:Matrix (Fin s) (Fin s) R}
    (strict:∀i j,i≤j→A i j=0) (hk:k≤s) (q:ℕ) :
    (zeroSpace A q).map (prefixRestrict hk)=zeroSpace (prefixMatrix A hk) q := by
  simp only [zeroSpace,Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_,⟨t,u,eq,ht,rfl⟩,rfl⟩
    exact ⟨t,u,eq,ht,by rw [map_sub,←normTree_prefix strict hk,←normTree_prefix strict hk]⟩
  · rintro ⟨t,u,eq,ht,rfl⟩
    exact ⟨_,⟨t,u,eq,ht,rfl⟩,by rw [map_sub,←normTree_prefix strict hk,←normTree_prefix strict hk]⟩

theorem rootStageResidual_mem {ι : Type*} [Fintype ι] (A:Matrix ι ι R)
    (t:FiniteRootedTree) : rootStageResidual A t∈zeroSpace A (t.order:ℕ) := by
  have e : (.leaf ◂ t).order=(clockTree (t.order:ℕ)).order := by
    apply PNat.eq
    simp [order,PNat.add_coe,Nat.add_comm]
  have ht : ((.leaf ◂ t).order:ℕ)≤(t.order:ℕ)+1 := by
    simp [order,PNat.add_coe,Nat.add_comm]
  have h:=normDiff_mem (j:=(t.order:ℕ)) A (.leaf ◂ t) (clockTree (t.order:ℕ)) e ht
  have f : normTree A (.leaf ◂ t)=(t.factorial:R) • (A*ᵥΦ t A) := by
    simp [normTree,forestFactorial,factorial]
  rw [f,normTree_clockTree] at h
  exact h

end Ring

section Field
variable {K : Type*} [Field K] {s:ℕ}

/-- A nonzero clean receiver really carries the full native reviewed
order conditions on its rescaled leading tableau. -/
theorem exact_receiver_prefix_order {A:Matrix (Fin s) (Fin s) K}
    (strict:∀i j,i≤j→A i j=0) (i:Fin s) (q:ℕ)
    (nz:nodes A i≠0) (clean:∀v∈zeroSpace A q,v i=0) :
    HasOrder q
      ((nodes A i)⁻¹ • prefixMatrix A i.isLt.le) (fun j:Fin i.val=>(nodes A i)⁻¹*A i (Fin.castLE i.isLt.le j)) := by
  intro t ht
  let r := (nodes A i)⁻¹
  let B := prefixMatrix A i.isLt.le
  let rb : Fin i.val→K := fun j=>r*A i (Fin.castLE i.isLt.le j)
  have hz := clean _ (zeroSpace_mono A ht (rootStageResidual_mem A t))
  have z : (t.factorial:K)*(A*ᵥΦ t A) i=(nodes A i)^(t.order:ℕ) := sub_eq_zero.mp hz
  have fact : r*r^((t.order:ℕ)-1)=r^(t.order:ℕ) := by
    rw [←pow_succ']
    congr 1
    have :=t.order.pos
    omega
  have mass : rb ⬝ᵥ Φ t (r•B)=r^(t.order:ℕ)*(A*ᵥΦ t A) i := by
    unfold B
    rw [Φ_smul,Φ_prefix strict i.isLt.le,dotProduct]
    simp only [rb,Pi.smul_apply,smul_eq_mul,prefixRestrict_apply]
    have terms (j:Fin i.val) :
      r*A i (Fin.castLE i.isLt.le j)*(r^((t.order:ℕ)-1)*Φ t A (Fin.castLE i.isLt.le j))=
      r^(t.order:ℕ)*(A i (Fin.castLE i.isLt.le j)*Φ t A (Fin.castLE i.isLt.le j)) := by
      rw [←fact];ac_rfl
    rw [Finset.sum_congr rfl (fun j _=>terms j),←Finset.mul_sum]
    rw [sum_prefix_zero_tail i.isLt.le (fun j=>A i j*Φ t A j)
      (fun j hj=>by rw [strict _ _ hj,zero_mul])]
    rfl
  change (t.factorial:K)*(rb ⬝ᵥ Φ t (r•B))=1
  rw [mass,mul_left_comm,z,←mul_pow]
  simp [r,nz]

end Field
end RKResearch.Certified.Graded
