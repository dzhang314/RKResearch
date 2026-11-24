module

public import RKCert.ReviewedNative.DIRKC2PrefixCompatibility
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

/-! # One-degree charge for the exact native exterior cut -/
namespace RKResearch.Certified.Graded.OuterHead

open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
variable {U : Submodule K (Fin s → K)} {w : Fin s → K}

private theorem dim_degreeLT (n : ℕ) : finrank K (degreeLT K n)=n := by
  rw [(degreeLTEquiv K n).finrank_eq,Module.finrank_fin_fun]

/-- A fixed prefix constraint cannot buy more than one head dimension
when the degree cap rises by one. -/
theorem compatible_degree_charge (H : Submodule K (K[X])) (k : ℕ) :
    finrank K (H ⊓ degreeLT K (k+1) : Submodule K (K[X])) ≤
      finrank K (H ⊓ degreeLT K k : Submodule K (K[X]))+1 := by
  let W := H ⊓ degreeLT K (k+1)
  let D := degreeLT K k
  let E := degreeLT K (k+1)
  have h : W≤E := inf_le_right
  have d : D≤E := degreeLT_mono (Nat.le_succ _)
  let : FiniteDimensional K D := Module.Finite.equiv (degreeLTEquiv K k).symm
  let : FiniteDimensional K E := Module.Finite.equiv (degreeLTEquiv K (k+1)).symm
  let : FiniteDimensional K W :=
    FiniteDimensional.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective _)
  have dm : W ⊓ D=H ⊓ D := by
    change H ⊓ E ⊓ D=H ⊓ D
    rw [inf_assoc,inf_eq_right.mpr d]
  have j := W.finrank_sup_add_finrank_inf_eq D
  rw [dm] at j
  have q := Submodule.finrank_mono (sup_le h d)
  have qD : finrank K D=k := dim_degreeLT _
  have qE : finrank K E=k+1 := dim_degreeLT _
  change finrank K W≤finrank K (H⊓D : Submodule K (K[X]))+1
  omega

variable [CharZero K]

set_option maxHeartbeats 900000 in
/-- One common nonzero origin-cleared scalar with a paid head correction,
and with its primitive vanishing at each earlier exterior knot and also
at the new refunded exterior clock. The input/output ranks are charged
on the same physical compatibility constraints. -/
theorem ExteriorStep.paired_cut {C : CoreMask A U} {k : ℕ}
    (D : ExteriorStep C (k+1)) (ha : A.IsLowerTriangular)
    (inside : U≤zeroSpace A (k+3))
    (flagIn : chain (diag (nodes A)) U w k≤zeroSpace A (k+3))
    (flagOut : zeroSpace A (k+4)≤chain (diag (nodes A)) U w (k+1))
    (refund : A D.next D.next=0) (dirty : ∀ j, w (D.old j)≠0) :
    ∃ P Q : K[X], P≠0 ∧ P.natDegree≤k+3 ∧ P.eval 0=0 ∧ Q.degree < (k:WithBot ℕ) ∧
      (∀ j, P.eval (nodes A (D.old j))=w (D.old j)*Q.eval (nodes A (D.old j))) ∧
      (primitive P).eval (nodes A D.next)=0 ∧ ∀ j, (primitive P).eval (nodes A (D.old j))=0 := by
  classical
  let H := C.compatible w D.next
  let V := degreeLT K (k+3)
  let W := H ⊓ degreeLT K k
  let Z := H ⊓ degreeLT K (k+1)
  let : FiniteDimensional K (degreeLT K k) := Module.Finite.equiv (degreeLTEquiv K k).symm
  let : FiniteDimensional K (degreeLT K (k+1)) := Module.Finite.equiv (degreeLTEquiv K (k+1)).symm
  let : FiniteDimensional K V := Module.Finite.equiv (degreeLTEquiv K (k+3)).symm
  let : FiniteDimensional K W := FiniteDimensional.of_injective
    (Submodule.inclusion (show W≤degreeLT K k from inf_le_right)) (Submodule.inclusion_injective _)
  let : FiniteDimensional K Z := FiniteDimensional.of_injective
    (Submodule.inclusion (show Z≤degreeLT K (k+1) from inf_le_right)) (Submodule.inclusion_injective _)
  let F : V→ₗ[K] K[X] := (LinearMap.mulLeft K X).comp V.subtype
  let ix : Fin ((k+1)+1) → Fin s := Fin.cons D.next D.old
  let O : K[X] →ₗ[K] (Fin (k+1)→K) := LinearMap.pi fun i => Polynomial.leval (nodes A (D.old i))
  let O' : K[X] →ₗ[K] (Fin ((k+1)+1)→K) := LinearMap.pi fun i => Polynomial.leval (nodes A (ix i))
  let H₁ := weightedEval (nodes A ∘ D.old) (w ∘ D.old)
  let H₂ := weightedEval (nodes A ∘ ix) (w ∘ ix)
  let L := (O.comp F).coprod (-(H₁.comp W.subtype))
  let G := O'.comp (primitive.comp F)
  let E := H₂.comp Z.subtype
  have degree (v : V) : (F v).natDegree≤k+3 := by
    change (X*(v:K[X])).natDegree≤k+3
    by_cases z : (v:K[X])=0
    · simp [z]
    rw [natDegree_X_mul z]
    have h := (natDegree_lt_iff_degree_lt z).mpr (mem_degreeLT.mp v.property)
    omega
  have origin (v : V) : (F v).eval 0=0 := by change (X*(v:K[X])).eval 0=0; simp
  have obs (v : V) (q : W) (ok : L (v,q)=0) (j : Fin (k+1)) :
      (F v).eval (nodes A (D.old j))=weightedEval (nodes A) w (q:K[X]) (D.old j) := by
    have h := congrFun ok j
    change (F v).eval (nodes A (D.old j)) + -(H₁ (q:K[X]) j) = 0 at h
    have e : H₁ (q:K[X]) j=weightedEval (nodes A) w (q:K[X]) (D.old j) := by simp [H₁]
    rwa [e,←sub_eq_add_neg,sub_eq_zero] at h
  have flow (v : V) (q : W) (ok : L (v,q)=0) : G v∈LinearMap.range E := by
    obtain ⟨a,pr⟩ := D.fit_full_prefix (origin v) q.property.1 (obs v q ok)
    let input := evalNodes A (F v)-weightedEval (nodes A) w (q:K[X])-a • C.mask
    have pre : ∀ j < D.next, input j=0 := by
      intro j hj
      simpa only [input,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using pr j hj
    have member : weightedEval (nodes A) w (q:K[X])∈zeroSpace A (k+3) :=
      flagIn (weighted_mem_chain (mem_degreeLT.mp q.property.2))
    have hd : input-evalNodes A (F v)∈zeroSpace A (k+3) := by
      convert (zeroSpace A (k+3)).neg_mem ((zeroSpace A (k+3)).add_mem member
        (inside (U.smul_mem a C.mem))) using 1
      dsimp [input]; abel
    obtain ⟨R,deg,compat,record⟩ := D.primitive_output ha flagOut (degree v) hd pre refund
    refine ⟨⟨R,compat,mem_degreeLT.mpr deg⟩,?_⟩
    ext j
    change weightedEval (nodes A) w R (ix j)=(primitive (F v)).eval (nodes A (ix j))
    exact Fin.cases (record _ le_rfl D.next_out).symm (fun l => (record _ (D.earlier l).le (D.old_out l)).symm) j
  let B : (LinearMap.ker L : Submodule K (V×W)) →ₗ[K] (Fin ((k+1)+1) → K) :=
    (G.comp (LinearMap.fst K V W)).comp (LinearMap.ker L).subtype
  have range : LinearMap.range B≤LinearMap.range E := by
    rintro _ ⟨⟨⟨v,q⟩,eq⟩,rfl⟩
    exact flow v q eq
  have lr := L.finrank_range_add_finrank_ker
  rw [Module.finrank_prod] at lr
  have br := LinearMap.finrank_range_add_finrank_ker (K:=K) (V:=↥(LinearMap.ker L)) B
  have er := LinearMap.finrank_range_le E
  have rr := Submodule.finrank_mono range
  have lm := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_fin_fun] at lm
  have big : finrank K V=k+3 := dim_degreeLT _
  have cost : finrank K Z≤finrank K W+1 := compatible_degree_charge H k
  have live : 0<finrank K (LinearMap.ker B) := by omega
  have nbot : LinearMap.ker B≠⊥ := by
    intro h
    rw [h,finrank_bot] at live
    exact (Nat.lt_irrefl _) live
  obtain ⟨⟨⟨v,q⟩,lq⟩,gp,nonzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot nbot
  have l0 : L (v,q)=0 := lq
  have g0 : G v=0 := gp
  have vne : v≠0 := by
    intro vz
    have qz (j : Fin (k+1)) : (q:K[X]).eval ((nodes A ∘ D.old) j)=0 := by
      have t := obs v q l0 j
      rw [vz,map_zero,eval_zero,weightedEval_apply] at t
      exact (mul_eq_zero.mp t.symm).resolve_right (dirty j)
    have dq := mem_degreeLT.mp q.property.2
    have q0 : (q:K[X])=0 := eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ D.distinct.injOn
      (by rw [Finset.card_univ,Fintype.card_fin]; exact dq.trans (by exact_mod_cast Nat.lt_succ_self k))
      (fun j _ => qz j)
    exact nonzero (Subtype.ext (Prod.ext vz (Subtype.ext q0)))
  have fne : F v≠0 := mul_ne_zero X_ne_zero (fun z => vne (Subtype.ext z))
  have read (j : Fin ((k+1)+1)) : (primitive (F v)).eval (nodes A (ix j))=0 := congrFun g0 j
  refine ⟨F v,q,fne,degree v,origin v,mem_degreeLT.mp q.property.2,fun j => ?_,read 0,fun j => read j.succ⟩
  simpa only [weightedEval_apply,mul_comm] using obs v q l0 j

end RKResearch.Certified.Graded.OuterHead
