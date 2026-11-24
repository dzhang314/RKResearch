module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
namespace RKCert.OneEscape
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
open Module
/-- Orbit remains inside F through the n-th iterate, including the initial vector. -/
def core (T : V →ₗ[K] V) (F : Submodule K V) : ℕ → Submodule K V
  | 0 => F
  | n+1 => core T F n ⊓ F.comap (T^(n+1))
@[simp] theorem core_zero (T : V →ₗ[K] V) (F : Submodule K V) : core T F 0=F := rfl
theorem descend (T : V →ₗ[K] V) (F : Submodule K V) (j : ℕ) :
    core T F (j+1) ≤ core T F j := inf_le_left
theorem mem_core {T : V →ₗ[K] V} {F : Submodule K V} {n : ℕ} {x : V} :
    x ∈ core T F n ↔ ∀ k ≤ n, (T^k) x ∈ F := by
  induction n with
  | zero => simp only [core_zero,Nat.le_zero,forall_eq,pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
  | succ n ih =>
    change (x ∈ core T F n ∧ (T^(n+1)) x ∈ F) ↔ _
    rw [ih]
    constructor
    · intro h k hk
      rcases Nat.eq_or_lt_of_le hk with rfl|hk
      · exact h.2
      · exact h.1 _ (by omega)
    · intro h
      exact ⟨fun k hk => h k (by omega),h _ le_rfl⟩
/-- A plateau makes this subspace genuinely invariant. -/
theorem invariant_of_plateau {T : V →ₗ[K] V} {F : Submodule K V} {n : ℕ}
    (h : core T F n = core T F (n+1)) : (core T F n).map T ≤ core T F n := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_core.mpr
  intro k hk
  have hz := mem_core.mp (h ▸ hx : x ∈ core T F (n+1)) (k+1) (by omega)
  simpa only [pow_succ,Module.End.mul_eq_comp,LinearMap.comp_apply] using hz
theorem invariant_le_core {T : V →ₗ[K] V} {F U : Submodule K V}
    (hin : U ≤ F) (hT : U.map T ≤ U) (n : ℕ) : U ≤ core T F n := by
  intro x hx
  apply mem_core.mpr
  intro k hk
  apply hin
  induction k with
  | zero => simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using hx
  | succ k ih =>
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact hT ⟨_,ih (by omega),rfl⟩
section Rank
variable [FiniteDimensional K V]
/-- Relative rank-nullity for successive clock preimages. -/
theorem core_rank_step (T : V →ₗ[K] V) (F : Submodule K V) (n : ℕ) :
    finrank K (core T F n) + finrank K F ≤
      finrank K (core T F (n+1)) + finrank K (F ⊔ F.map T : Submodule K V) := by
  let U := core T F n
  let W := F ⊔ F.map T
  let a := (F.mkQ.comp (T^(n+1))).domRestrict U
  let e := F.mkQ.domRestrict W
  have hsub : LinearMap.range a ≤ LinearMap.range e := by
    rintro _ ⟨x,rfl⟩
    have hx := mem_core.mp x.property n le_rfl
    have hz : (T^(n+1)) x.val ∈ W := by
      rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      exact (le_sup_right : F.map T ≤ W) ⟨_,hx,rfl⟩
    exact ⟨⟨_,hz⟩,rfl⟩
  have ha : LinearMap.ker a = (core T F (n+1)).comap U.subtype := by
    ext x
    change F.mkQ ((T^(n+1)) x.val)=0 ↔ (x.val∈core T F n ∧ (T^(n+1)) x.val∈F)
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact ⟨fun h => ⟨x.property,h⟩,And.right⟩
  have he : LinearMap.ker e = F.comap W.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero F
  have r1 := a.finrank_range_add_finrank_ker
  have r2 := e.finrank_range_add_finrank_ker
  rw [ha,(Submodule.comapSubtypeEquivOfLe (descend T F n)).finrank_eq] at r1
  rw [he,(Submodule.comapSubtypeEquivOfLe (le_sup_left : F≤W)).finrank_eq] at r2
  have r3 := Submodule.finrank_mono hsub
  change finrank K U+finrank K F ≤ _ +finrank K W
  omega
theorem unit_loss {T : V →ₗ[K] V} {F : Submodule K V}
    (one : finrank K (F⊔F.map T : Submodule K V) ≤ finrank K F+1) (n : ℕ)
    (hne : core T F n ≠ core T F (n+1)) :
    finrank K (core T F n) = finrank K (core T F (n+1))+1 := by
  have hr := core_rank_step T F n
  have hs := Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne (descend T F n) (Ne.symm hne))
  omega

/-- The invariant core is reached after at most dim(F) checks. -/
theorem exists_plateau (T : V →ₗ[K] V) (F : Submodule K V) :
    ∃ n ≤ finrank K F, core T F n = core T F (n+1) := by
  by_contra hh
  have de (n : ℕ) (hn : n ≤ finrank K F) :
      finrank K (core T F (n+1)) < finrank K (core T F n) := by
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne (descend T F n) (fun e => hh ⟨n,hn,e.symm⟩)
  have bound (n : ℕ) (hn : n ≤ finrank K F+1) :
      finrank K (core T F n)+n ≤ finrank K F := by
    induction n with
    | zero => rw [core_zero,Nat.add_zero]
    | succ n ih =>
      have h1 := ih (by omega)
      have h2 := de n (by omega)
      omega
  have := bound (finrank K F+1) le_rfl
  omega

/-- The span of an existing invariant part plus the first r powers of one vector. -/
def chain (T : V →ₗ[K] V) (U : Submodule K V) (w : V) : ℕ → Submodule K V
  | 0 => U
  | j+1 => chain T U w j ⊔ Submodule.span K {(T^j) w}

/-- Intrinsic one-clock-escape normal form. The proof explicitly supplies the
largest T-invariant part of F, one genuine vector w, all r cheap powers, the
first *unpaid* power outside F, and the exact rank. No Euclidean orthogonality
or restriction on the eigenvalues of T is used. -/
theorem single_head {T : V →ₗ[K] V} {F : Submodule K V}
    (one : finrank K (F⊔F.map T : Submodule K V) ≤ finrank K F+1)
    (out : ¬ F.map T ≤ F) :
    ∃ (r : ℕ) (U : Submodule K V) (w : V),
      0 < r ∧ U.map T ≤ U ∧ U ≤ F ∧
      (∀ S : Submodule K V, S.map T ≤ S → S ≤ F → S ≤ U) ∧
      F = chain T U w r ∧
      (∀ j < r, (T^j) w ∈ F) ∧ (T^r) w ∉ F ∧
      finrank K F = finrank K U+r := by
  classical
  obtain ⟨n,_,hn⟩ := exists_plateau T F
  have ex : ∃ k, core T F k = core T F (k+1) := ⟨n,hn⟩
  let r := Nat.find ex
  have hr : core T F r = core T F (r+1) := Nat.find_spec ex
  have prev (j : ℕ) (hj : j<r) : core T F j ≠ core T F (j+1) := Nat.find_min ex hj
  have hpos : 0<r := by
    by_contra he
    have hzero : r=0 := by omega
    rw [hzero] at hr
    exact out (invariant_of_plateau hr)
  let U := core T F r
  have hri : r-1+1=r := by omega
  have lack : ¬ core T F (r-1) ≤ core T F r := by
    intro h
    apply prev (r-1) (by omega)
    rw [hri]
    exact le_antisymm h (hri ▸ descend T F (r-1))
  obtain ⟨w,hw,hw'⟩ := Set.not_subset.mp (show ¬(core T F (r-1) : Set V) ⊆ core T F r from lack)
  have paid (j : ℕ) (hj : j<r) : (T^j) w ∈ F :=
    mem_core.mp hw j (by omega)
  have unpaid : (T^r) w ∉ F := by
    intro h
    apply hw'
    rw [← hri]
    exact ⟨hw,hri.symm ▸ h⟩
  have dims (j : ℕ) (hj : j ≤ r) :
      finrank K (core T F (r-j)) = finrank K U+j := by
    induction j with
    | zero => simp [U]
    | succ j ih =>
      have e := ih (by omega)
      have h := unit_loss one (r-(j+1)) (prev _ (by omega))
      rw [show r-(j+1)+1=r-j by omega] at h
      omega
  have hc (j : ℕ) (hj : j ≤ r) : chain T U w j = core T F (r-j) := by
    induction j with
    | zero => simp [chain,U]
    | succ j ih =>
      have hstep : r-(j+1)+1=r-j := by omega
      have hnow : (T^j) w ∈ core T F (r-(j+1)) := by
        apply mem_core.mpr
        intro k hk
        have hp := paid (k+j) (by omega)
        simpa only [pow_add,Module.End.mul_eq_comp,LinearMap.comp_apply] using hp
      have hnot : (T^j) w ∉ core T F (r-j) := by
        intro h
        have he := mem_core.mp h (r-j) le_rfl
        apply unpaid
        rw [← show r-j+j=r by omega,pow_add,Module.End.mul_eq_comp,LinearMap.comp_apply]
        exact he
      change chain T U w j ⊔ Submodule.span K {(T^j) w} = _
      rw [ih (by omega)]
      apply Submodule.eq_of_le_of_finrank_le
      · apply sup_le _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hnow)
        exact hstep ▸ descend T F (r-(j+1))
      · rw [Submodule.finrank_sup_span_singleton hnot]
        have h := unit_loss one (r-(j+1)) (prev _ (by omega))
        rw [hstep] at h
        exact h.le
  refine ⟨r,U,w,hpos,invariant_of_plateau hr,?_,?_,?_,paid,unpaid,?_⟩
  · intro x hx
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using mem_core.mp hx 0 (Nat.zero_le r)
  · intro S hs hin
    exact invariant_le_core hin hs r
  · simpa only [Nat.sub_self,core_zero] using (hc r le_rfl).symm
  · have hdim := dims r le_rfl
    rw [Nat.sub_self r,core_zero] at hdim
    exact hdim

end Rank
end RKCert.OneEscape

