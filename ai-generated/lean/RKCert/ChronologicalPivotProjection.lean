module

public import RKCert.DirkPolynomialMarked
public import RKCert.HeadChart

@[expose] public section

/-! # One-node chronological pivot projection
This is an exact projection on original vectors, implemented with a padded
zero pivot rather than a shortened tableau. It preserves chronology and a
split clock, and charges the primitive and commutator errors explicitly. -/
namespace RKCert.Paired.PivotProjection
open RKCert.Endpoint RKCert.OneEscape Polynomial
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {c d : Vec K s} {i : Fin s} {ord : Fin s ≃ Fin s}

def coefficient (d : Vec K s) (i : Fin s) (x : Vec K s) : K := x i / d i

def remove (d : Vec K s) (i : Fin s) : Vec K s →ₗ[K] Vec K s :=
  LinearMap.id-(LinearMap.proj i).smulRight ((d i)⁻¹ • d)

theorem remove_apply (d x : Vec K s) (i : Fin s) :
    remove d i x=x-coefficient d i x • d := by
  simp [remove,coefficient,div_eq_mul_inv,smul_smul]

theorem remove_pivot (hi : d i≠0) (x : Vec K s) : remove d i x i=0 := by
  rw [remove_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,coefficient,div_mul_cancel₀ _ hi,sub_self]

theorem remove_kills (hi : d i≠0) : remove d i d=0 := by
  rw [remove_apply,coefficient,div_self hi,one_smul,sub_self]

theorem remove_idempotent (hi : d i≠0) (x : Vec K s) : remove d i (remove d i x)=remove d i x := by
  conv_lhs => rw [remove_apply]
  simp [coefficient,remove_pivot hi]

/-- Since d has an actual zero prefix, removal does not introduce a future
dependence in the chronological linear operator. -/
theorem remove_causal (hi : d i≠0) (pref : ∀ j, (ord j).val < (ord i).val → d j=0) :
    CausalDiag ord (remove d i) (fun j => if j=i then 0 else 1) := by
  intro j x hx
  by_cases hji : j=i
  · subst j
    simp [remove_pivot hi]
  · change remove d i x j=(if j=i then (0:K) else 1)*x j
    rw [ite_eq_right hji,one_mul,remove_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    by_cases h : (ord j).val < (ord i).val
    · simp [pref j h]
    · have hl : (ord i).val < (ord j).val := lt_of_le_of_ne (le_of_not_gt h)
        (fun e => hji (ord.injective (Fin.ext e.symm)))
      simp [coefficient,hx i hl]

theorem causal_comp {N M : Vec K s →ₗ[K] Vec K s} {a b : Vec K s}
    (hN : CausalDiag ord N a) (hM : CausalDiag ord M b) :
    CausalDiag ord (N.comp M) (a*b) := by
  intro j x hx
  have hz (k : Fin s) (hk : (ord k).val < (ord j).val) : M x k=0 := by
    rw [hM k x (fun l hl => hx l (hl.trans hk)),hx k hk,mul_zero]
  rw [LinearMap.comp_apply,hN j (M x) hz,hM j x hx,Pi.mul_apply,mul_assoc]

/-- Node-local removal commutes with the true clock. -/
theorem remove_clock (loc : ∀ j, c j≠c i → d j=0) (x : Vec K s) :
    remove d i (diag c x)=diag c (remove d i x) := by
  ext j
  simp only [remove_apply,diag_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,coefficient]
  by_cases he : c j=c i
  · rw [he]
    ring
  · simp [loc j he]

theorem remove_weighted (loc : ∀ j, c j≠c i → d j=0) (x : Vec K s) (P : K[X]) :
    remove d i (weightedEval c x P)=weightedEval c (remove d i x) P := by
  ext j
  simp only [remove_apply,weightedEval_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,coefficient]
  by_cases he : c j=c i
  · rw [he]
    ring
  · simp [loc j he]

theorem remove_sum (hd : row d 1=0) (x : Vec K s) :
    row (remove d i x) 1=row x 1 := by
  rw [remove_apply]
  change rowL (x-coefficient d i x • d) 1=rowL x 1
  rw [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,rowL_apply,rowL_apply,
    hd,mul_zero,sub_zero]

def contracted (N : Vec K s →ₗ[K] Vec K s) (d : Vec K s) (i : Fin s) :
    Vec K s →ₗ[K] Vec K s :=
  (remove d i).comp (N.comp (remove d i))

theorem contracted_causal {N : Vec K s →ₗ[K] Vec K s} {a : Vec K s}
    (ha : CausalDiag ord N a) (hi : d i≠0)
    (pref : ∀ j, (ord j).val < (ord i).val → d j=0) :
    CausalDiag ord (contracted N d i) (fun j => if j=i then 0 else a j) := by
  have hP := remove_causal hi pref
  have hc := causal_comp hP (causal_comp ha hP)
  have eq : (fun j => if j=i then 0 else a j)=
      (fun j => if j=i then 0 else 1)*(a*(fun j => if j=i then 0 else 1)) := by
    ext j
    by_cases e : j=i <;> simp [e]
  rw [contracted,eq]
  exact hc

/-- The exact primitive defect introduced by the projection is a multiple
of the true projected N d, not a primitive error of an assumed shortened
method. -/
theorem contracted_apply_remove (N : Vec K s →ₗ[K] Vec K s) (hi : d i≠0) (x : Vec K s) :
    contracted N d i (remove d i x) =
      remove d i (N x)-coefficient d i x • remove d i (N d) := by
  change remove d i (N (remove d i (remove d i x)))=_
  rw [remove_idempotent hi (x:=x)]
  calc
    remove d i (N (remove d i x)) = remove d i (N (x-coefficient d i x • d)) :=
      congrArg (fun z => remove d i (N z)) (remove_apply d x i)
    _ = _ := by rw [map_sub,map_smul,map_sub,map_smul]

/-- The exact commutator discrepancy is confined to three charged
directions. This formula uses the actual chronological contracted operator. -/
theorem contracted_commutator_error (N : Vec K s →ₗ[K] Vec K s) (hi : d i≠0)
    (loc : ∀ j, c j≠c i → d j=0) (x : Vec K s) :
    commutatorR (contracted N d i) (diag c) (remove d i x) -
      remove d i (commutatorR N (diag c) x) =
      (coefficient d i (diag c x)+coefficient d i (N x)-
        coefficient d i x*coefficient d i (N d)) • remove d i (N d)
        - coefficient d i x • remove d i (diag c (N d)) +
        coefficient d i x • remove d i (N (N d)) := by
  simp only [commutatorR,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,
    contracted_apply_remove N hi,map_smul,←remove_clock loc,smul_sub,smul_smul,add_smul,sub_smul]
  abel

theorem projected_chain (hi : d i≠0) (loc : ∀ j, c j≠c i → d j=0)
    (w : Vec K s) (n : ℕ) :
    (chain (diag c) (Submodule.span K ({d}:Set (Vec K s))) w n).map (remove d i) =
      chain (diag c) ⊥ (remove d i w) n := by
  have hp (r : ℕ) : remove d i ((diag c^r) w)=(diag c^r) (remove d i w) := by
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,remove_clock loc,ih]
  induction n with
  | zero => simp [chain,Submodule.map_span,Set.image_singleton,remove_kills hi]
  | succ n ih =>
    rw [chain,Submodule.map_sup,ih,Submodule.map_span,Set.image_singleton,hp,chain]

end
end RKCert.Paired.PivotProjection
