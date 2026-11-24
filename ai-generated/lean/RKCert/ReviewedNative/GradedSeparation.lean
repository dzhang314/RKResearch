module
public import RKCert.ReviewedNative.GradedDefects
public import RKCert.ReviewedNative.FiniteCauchy
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Native polynomial-plus-defect decomposition and exact midpoint rank -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree Module
open scoped FiniteRootedTree Matrix

section Ring
variable {ι R : Type*} [Fintype ι] [CommRing R]
variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- The genuine stage evaluations of coefficient vectors through degree q. -/
def coeffEval (A : Matrix ι ι R) (q : ℕ) : (Fin (q+1) → R) →ₗ[R] (ι→R) :=
  Fintype.linearCombination R (fun j:Fin (q+1) => normTree A (clockTree j.val))

theorem coeffEval_apply (A : Matrix ι ι R) (q : ℕ) (a : Fin (q+1)→R) :
    coeffEval A q a=∑ j:Fin (q+1),a j • normTree A (clockTree j.val) := rfl

theorem coeffEval_single (A : Matrix ι ι R) (q : ℕ) (j : Fin (q+1)) :
    coeffEval A q (Pi.single j 1)=normTree A (clockTree j.val) := by
  rw [coeffEval,Fintype.linearCombination_apply_single,one_smul]

theorem coeffEval_mem_treeSpace (A : Matrix ι ι R) (q : ℕ) (a : Fin (q+1)→R) :
    coeffEval A q a∈treeSpace A q := by
  rw [coeffEval_apply]
  apply (treeSpace A q).sum_mem
  intro j _
  apply (treeSpace A q).smul_mem
  apply (treeSpace A q).smul_mem
  exact Φ_mem_treeSpace A _ (by rw [order_clockTree]; have :=j.isLt; omega)

/-- Tree space is literally the sum of the clock polynomial image and the
homogeneous defect span. The forest-factorial unit is derived from order. -/
theorem treeSpace_coeff_sup (ho:HasOrder A b p) {q:ℕ} (pay:q+1≤p) :
    treeSpace A q=(coeffEval A q).range⊔zeroSpace A q := by
  apply le_antisymm _ (sup_le ?_ (zeroSpace_le_treeSpace A q))
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,rfl⟩
    have hpos := t.order.pos
    let j : Fin (q+1) := ⟨(t.order:ℕ)-1,by omega⟩
    have horder : t.order=(clockTree j.val).order := by
      apply PNat.eq
      rw [order_clockTree]
      dsimp [j]
      omega
    let B := (coeffEval A q).range⊔zeroSpace A q
    have k : normTree A (clockTree j.val)∈B :=
      (show (coeffEval A q).range≤B from le_sup_left) ⟨_,coeffEval_single A q j⟩
    have d : normTree A t-normTree A (clockTree j.val)∈B :=
      (show zeroSpace A q≤B from le_sup_right) (normDiff_mem A _ _ horder ht)
    have z : normTree A t∈B := by simpa using B.add_mem d k
    exact (B.smul_mem_iff_of_isUnit (forestFactorial_isUnit ho t (ht.trans pay))).mp z
  · rintro _ ⟨a,rfl⟩
    exact coeffEval_mem_treeSpace A _ a

theorem coeffEval_origin {s:ℕ} {A:Matrix (Fin (s+1)) (Fin (s+1)) R}
    (strict:∀i j,i≤j→A i j=0) (q:ℕ) (a:Fin (q+1)→R) :
    coeffEval A q a 0=a 0 := by
  have h (j:Fin (s+1)) : A 0 j=0 := strict 0 j (Fin.zero_le _)
  have c : nodes A 0=0 := by simp [nodes,Matrix.mulVec,dotProduct,h]
  rw [coeffEval_apply,Fin.sum_univ_succ]
  simp only [normTree_clockTree,Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,c]
  simp

end Ring

section Field
variable {ι K : Type*} [Fintype ι] [Field K]
variable {A : Matrix ι ι K} {b : ι → K} {p : ℕ}

theorem probe_coeffEval (ho:HasOrder A b p) {k q:ℕ} (pay:k+q+1≤p)
    (a:Fin (q+1)→K) :
    probe A b k (coeffEval A q a)=∑ j:Fin (q+1),a j/((k+j.val+1:ℕ):K) := by
  rw [coeffEval_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := probe_normTree ho (clockTree j.val) k (by rw [order_clockTree];have :=j.isLt;omega)
  rw [order_clockTree,←Nat.add_assoc] at h
  rw [map_smul,smul_eq_mul]
  apply (eq_div_iff (IsUnit.of_mul_eq_one _ h).ne_zero).mpr
  calc
    _ = a j * (((k+j.val+1:ℕ):K)*probe A b k (normTree A (clockTree j.val))) := by ac_rfl
    _ = _ := by rw [h,mul_one]

theorem moments_detect (ho:HasOrder A b p) {n d:ℕ} (hd:0<d)
    (hn:n≤p+1) (pay:∀i j:Fin n,i.val+j.val+d≤p)
    (a:Fin n→K) (test:∀i:Fin n,(∑j:Fin n,a j/((i.val+j.val+d:ℕ):K))=0) :
    ∀j,a j=0 := by
  have apart (l r:ℕ) (lr:l<r) (hr:r-l≤p) : (l:K)≠(r:K) := by
    have unit := (ho.natCast_isUnit (by omega : 0<r-l) hr).ne_zero
    intro e
    rw [Nat.cast_sub lr.le,e,sub_self] at unit
    exact unit rfl
  have inj : Function.Injective (fun i:Fin n=>(i.val:K)) := by
    intro i j h
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with e|e|e
    · exact (apart _ _ e (by omega) h).elim
    · exact e
    · exact (apart _ _ e (by omega) h.symm).elim
  apply cauchy_kernel (fun i:Fin n=>(i.val:K)) (fun j:Fin n=>(j.val:K)+(d:K)) a inj
  · intro i j e; exact inj (add_right_cancel e)
  · intro i j
    have positive : 0 < i.val+j.val+d := by omega
    have un := (ho.natCast_isUnit positive (pay i j)).ne_zero
    simpa only [Nat.cast_add,add_assoc] using un
  · intro i
    simpa only [Nat.cast_add,add_assoc] using test i

theorem coeff_separated (ho:HasOrder A b p) {q:ℕ} (pay:2*q+1≤p)
    (a:Fin (q+1)→K) (h:coeffEval A q a∈zeroSpace A q) : a=0 := by
  ext j
  apply moments_detect ho (d:=1) (by decide) (by omega) (fun i j=>by omega) a _ j
  intro i
  have ev : probe A b i.val (coeffEval A q a)=0 := probe_zeroSpace ho (by omega) h
  rwa [probe_coeffEval ho (by omega)] at ev

/-- The explicit origin saves one row of Cauchy moments at an even
midpoint; all tree and matrix inputs are the native reviewed ones. -/
theorem explicit_coeff_separated {s:ℕ} {A:Matrix (Fin (s+1)) (Fin (s+1)) K}
    {b:Fin (s+1)→K} (strict:∀i j,i≤j→A i j=0) (ho:HasOrder A b p)
    {q:ℕ} (pay:2*q≤p) (a:Fin (q+1)→K) (h:coeffEval A q a∈zeroSpace A q) :
    a=0 := by
  have z : coeffEval A q a 0=0 := origin_zeroSpace strict q h
  rw [coeffEval_origin strict] at z
  have ev (i:Fin q) :
      (∑ j:Fin q,a j.succ/((i.val+j.val+2:ℕ):K))=0 := by
    have e : probe A b i.val (coeffEval A q a)=0 := probe_zeroSpace ho (by omega) h
    rw [probe_coeffEval ho (by omega),Fin.sum_univ_succ,z,zero_div,zero_add] at e
    simpa only [Fin.val_succ,Nat.add_assoc] using e
  have rest := moments_detect ho (d:=2) (by decide) (by omega)
    (fun i j=>by have :=i.isLt;have :=j.isLt;omega) (fun j:Fin q => a j.succ) ev
  ext j
  exact Fin.cases z rest j

theorem treeSpace_rank_eq_of_separation (ho:HasOrder A b p) {q:ℕ} (pay:q+1≤p)
    (sep:∀a,coeffEval A q a∈zeroSpace A q→a=0) :
    finrank K (treeSpace A q)=q+1+finrank K (zeroSpace A q) := by
  let V := (coeffEval A q).range
  let F := zeroSpace A q
  have dis : V⊓F=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨hv,hf⟩:=Submodule.mem_inf.mp hv
    obtain ⟨a,rfl⟩:=hv
    rw [sep a hf,map_zero]
    exact (⊥:Submodule K (ι→K)).zero_mem
  have hin : Function.Injective (coeffEval A q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    exact sep a (ha ▸ (F.zero_mem))
  have rV : finrank K V=q+1 := by
    unfold V
    rw [LinearMap.finrank_range_of_inj hin,Module.finrank_fin_fun]
  have z := Submodule.finrank_sup_add_finrank_inf_eq V F
  rw [dis,finrank_bot,add_zero,rV] at z
  rw [treeSpace_coeff_sup ho pay]
  exact z

theorem explicit_midpoint_rank_eq {s:ℕ} {A:Matrix (Fin (s+1)) (Fin (s+1)) K}
    {b:Fin (s+1)→K} (strict:∀i j,i≤j→A i j=0) (ho:HasOrder A b p)
    {q:ℕ} (pay:q+1≤p) (mid:2*q≤p) :
    finrank K (treeSpace A q)=q+1+finrank K (zeroSpace A q) :=
  treeSpace_rank_eq_of_separation ho pay (explicit_coeff_separated strict ho mid)

end Field
end RKResearch.Certified.Graded
