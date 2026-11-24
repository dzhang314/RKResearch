module

public import RKCert.Dirk15MinimalVisible
public import RKCert.Dirk15MinimalDeletedHead

@[expose] public section

/-! # The true grade-four quartic along the cheap ordinary head

Two extra ordinary clock multiplications of a genuine grade-four column
are still paid at grade six. A visible quartic therefore has a constant
head when the core has dimension two, and at most an affine head when it
has dimension one. These are original, not terminal-deleted, assertions.
-/
namespace RKCert.Paired
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]

section HeadCoordinates
variable {n : ℕ} {c w : Vec K n} {U : Submodule K (Vec K n)}

theorem weighted_head_eval_pow (k : ℕ) :
    weightedEval c w (X^k)=(diag c^k) w := by
  ext i
  simp only [weightedEval_apply,eval_pow,eval_X,Clock.pow_diag_apply]

theorem weighted_head_eval_clock (P : K[X]) :
    diag c (weightedEval c w P)=weightedEval c w (X*P) := by
  ext i
  simp only [diag_apply,weightedEval_apply,eval_mul,eval_X]
  ring

theorem weighted_eval_head_lt {P : K[X]} {r : ℕ} (dP : P.natDegree<r) :
    weightedEval c w P∈chain (diag c) U w r := by
  rw [P.as_sum_range' r dP]
  rw [map_sum]
  apply (chain (diag c) U w r).sum_mem
  intro j hj
  rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul,weighted_head_eval_pow]
  exact (chain (diag c) U w r).smul_mem _ (((chain_le_iff _).mp le_rfl).2 j
    (Finset.mem_range.mp hj))

theorem head_pow_ne_of_late {r t : ℕ} (inv : U.map (diag c)≤U)
    (pay : t≤r) (late : ((diag c)^r) w∉chain (diag c) U w r) :
    ((diag c)^t) w∉chain (diag c) U w t := by
  intro stall
  let T := diag c
  let F := chain T U w t
  have become : chain T U w (t+1)≤F := by
    change F⊔K∙((T^t) w)≤F
    exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).mpr stall)
  have invariant : F.map T≤F := by
    by_cases t0 : t=0
    · subst t
      exact inv
    · have ee : F⊔F.map T=chain T U w (t+1) :=
        chain_sup_map inv (Nat.pos_of_ne_zero t0)
      exact le_sup_right.trans (ee ▸ become)
  have start : w∈F := by
    by_cases t0 : t=0
    · change w∈chain (diag c) U w t
      simpa only [t0,pow_zero,one_apply_eq_self] using stall
    · have q := ((chain_le_iff (T:=T) (U:=U) (w:=w) t).mp le_rfl).2 0
        (Nat.pos_of_ne_zero t0)
      simpa only [pow_zero,one_apply_eq_self] using q
  have powers (k : ℕ) : (T^k) w∈F := by
    induction k with
    | zero => simpa only [pow_zero,one_apply_eq_self]
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp]
      exact invariant (Submodule.mem_map_of_mem ih)
  exact late (clock_chain_mono pay (powers r))

theorem weighted_head_eval_injective_mod {r : ℕ} (inv : U.map (diag c)≤U)
    (late : ((diag c)^r) w∉chain (diag c) U w r)
    {P : K[X]} (dP : P.natDegree<r) (mem : weightedEval c w P∈U) : P=0 := by
  by_contra pn
  let d := P.natDegree
  let T := diag c
  let Z := chain T U w d
  have hd := P.as_sum_range' (d+1) (Nat.lt_succ_self d)
  rw [Finset.sum_range_succ] at hd
  have e := congrArg (weightedEval c w) hd
  have split : weightedEval c w P = weightedEval c w (∑ k∈Finset.range d, monomial k (P.coeff k)) +
      P.coeff d • (T^d) w := by
    have h : weightedEval c w (monomial d (P.coeff d))=P.coeff d • (T^d) w := by
      rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul,weighted_head_eval_pow]
    rw [map_add,h] at e
    exact e
  have small : weightedEval c w (∑ k∈Finset.range d, monomial k (P.coeff k))∈Z := by
    rw [map_sum]
    apply Z.sum_mem
    intro k hk
    rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul,weighted_head_eval_pow]
    exact Z.smul_mem _ (((chain_le_iff (T:=T) (U:=U) (w:=w) d).mp le_rfl).2 k
      (Finset.mem_range.mp hk))
  have pure : weightedEval c w P∈Z :=
    ((chain_le_iff (T:=T) (U:=U) (w:=w) d).mp le_rfl).1 mem
  have memb : P.coeff d • (T^d) w∈Z := by
    have q := Z.sub_mem pure small
    rwa [split,add_sub_cancel_left] at q
  have nz : P.coeff d≠0 := by
    change P.coeff P.natDegree≠0
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr pn
  exact head_pow_ne_of_late inv (Nat.le_of_lt dP) late
    ((Z.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nz)).mp memb)

theorem weighted_head_coordinates_unique {r : ℕ} (inv : U.map (diag c)≤U)
    (late : ((diag c)^r) w∉chain (diag c) U w r)
    {P Q : K[X]} (p : P.natDegree<r) (q : Q.natDegree<r)
    {u z : Vec K n} (hu : u∈U) (hz : z∈U)
    (eq : u+weightedEval c w P=z+weightedEval c w Q) : P=Q := by
  apply sub_eq_zero.mp
  apply weighted_head_eval_injective_mod inv late ((natDegree_sub_le _ _).trans_lt (max_lt p q))
  rw [map_sub,show weightedEval c w P-weightedEval c w Q=z-u by
    linear_combination eq]
  exact U.sub_mem hz hu

end HeadCoordinates

variable [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

set_option maxHeartbeats 1400000 in
theorem Order15MinimalHead.visible_head_degree (h : Order15MinimalHead A b)
    {v : Vec K 20} (hv : v∈zeroSpace A 4) (out : v∉h.U) :
    ∃ u∈h.U, ∃ S : K[X], S≠0 ∧ S.natDegree≤2-finrank K h.U ∧
      v=u+weightedEval (nodes A) h.w S := by
  let F := zeroSpace A
  let c := nodes A
  let C' := diag c
  let U := h.U
  let w := h.w
  let E := weightedEval c w
  let r := h.length
  have dU : finrank K U≤2 := h.high
  have lU : 1≤finrank K U := h.low
  have len : r=6-finrank K U := rfl
  have eq : F 6=chain C' U w (r-1) := by
    have u := h.six
    have er : 5-finrank K U=r-1 := by omega
    change F 6=chain C' U w (5-finrank K U) at u
    rwa [er] at u
  have ek : F 7=chain C' U w r := h.seven
  have late : (C'^r) w∉chain C' U w r := by rw [←ek]; exact h.length_next_unpaid
  have parts {x : Vec K 20} (inc : x∈F 6) :
      ∃ u∈U,∃ P : K[X],P.natDegree<r-1 ∧ x=u+E P := by
    rw [eq] at inc
    obtain ⟨u,hu,P,pd,hP⟩ := Clock.exists_head_poly inc
    refine ⟨u,hu,P,?_ ,?_⟩
    · by_cases e : P=0
      · rw [e,natDegree_zero]
        omega
      · exact (natDegree_lt_iff_degree_lt e).mpr pd
    · ext i
      change x i=u i+weightedEval c w P i
      rw [weightedEval_apply]
      exact hP i
  have power2 : C' (C' v)∈F 6 := diag_zeroSpace A 5 (diag_zeroSpace A 4 hv)
  obtain ⟨u,hu,S,dS,eS⟩ := parts (zeroSpace_mono A (by decide : 4≤6) hv)
  obtain ⟨u₁,hu₁,S₁,dS₁,eS₁⟩ := parts
    (zeroSpace_mono A (by decide : 5≤6) (diag_zeroSpace A 4 hv))
  obtain ⟨u₂,hu₂,S₂,dS₂,eS₂⟩ := parts power2
  have invari {x : Vec K 20} (hx : x∈U) : C' x∈U :=
    h.maximal.2.1 (Submodule.mem_map_of_mem hx)
  have step₁ : X*S=S₁ := by
    have dd : (X*S).natDegree<r := by
      have t := natDegree_mul_le (p:=(X:K[X])) (q:=S)
      rw [natDegree_X] at t
      omega
    have ee : C' u+E (X*S)=u₁+E S₁ := by
      have x : C' (E S)=E (X*S) := weighted_head_eval_clock S
      rwa [←eS₁,←x,←map_add,←eS]
    exact weighted_head_coordinates_unique h.maximal.2.1 late dd (dS₁.trans (by omega))
      (invari hu) hu₁ ee
  have step₂ : X*S₁=S₂ := by
    have dd : (X*S₁).natDegree<r := by
      have t := natDegree_mul_le (p:=(X:K[X])) (q:=S₁)
      rw [natDegree_X] at t
      omega
    have ee : C' u₁+E (X*S₁)=u₂+E S₂ := by
      have x : C' (E S₁)=E (X*S₁) := weighted_head_eval_clock S₁
      rwa [←eS₂,←x,←map_add,←eS₁]
    exact weighted_head_coordinates_unique h.maximal.2.1 late dd (dS₂.trans (by omega))
      (invari hu₁) hu₂ ee
  have nz : S≠0 := by
    intro z
    apply out
    rwa [eS,z,map_zero,add_zero]
  have n₁ : S₁≠0 := step₁ ▸ mul_ne_zero X_ne_zero nz
  rw [←step₂,natDegree_mul X_ne_zero n₁,natDegree_X,←step₁,
    natDegree_mul X_ne_zero nz,natDegree_X] at dS₂
  have c : S.natDegree≤2-finrank K U := by omega
  exact ⟨u,hu,S,nz,c,eS⟩

end
end RKCert.Paired
