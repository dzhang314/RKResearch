module
public import RKCert.DiagonalHead
public import RKCert.GradedProducts

@[expose] public section
namespace RKCert.OneEscape
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {T : V →ₗ[K] V} {U : Submodule K V} {w : V}

theorem chain_sup_map (hU : U.map T≤U) {n : ℕ} (hn : 0<n) :
    chain T U w n ⊔ (chain T U w n).map T = chain T U w (n+1) := by
  have hR := (chain_le_iff (T:=T) (U:=U) (w:=w) (n+1)).mp le_rfl
  have hL := (chain_le_iff (T:=T) (U:=U) (w:=w) n).mp le_rfl
  apply le_antisymm
  · apply sup_le
    · exact (chain_le_iff _).mpr ⟨hR.1,fun k hk => hR.2 k (by omega)⟩
    · apply Submodule.map_le_iff_le_comap.mpr
      apply (chain_le_iff _).mpr
      constructor
      · intro u hu
        exact hR.1 (hU ⟨_,hu,rfl⟩)
      · intro k hk
        change T ((T^k) w) ∈ chain T U w (n+1)
        change (T * T^k) w ∈ _
        rw [←pow_succ']
        exact hR.2 _ (by omega)
  · apply (chain_le_iff _).mpr
    refine ⟨le_trans hL.1 le_sup_left,fun k hk => ?_⟩
    by_cases he : k<n
    · exact (le_sup_left : chain T U w n ≤ _) (hL.2 _ he)
    · have ek : k=(n-1)+1 := by omega
      rw [ek,pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      apply (le_sup_right : (chain T U w n).map T ≤ _)
      exact ⟨_,hL.2 _ (by omega),rfl⟩
end RKCert.OneEscape

namespace RKCert.Paired.Clock
open RKCert.Paired RKCert.OneEscape Module
variable {K : Type*} [Field K] {s : ℕ} {c : Vec K s}
variable {U : Submodule K (Vec K s)} {w x : Vec K s}

/-- The head part of each vector in a length-n chain is one scalar polynomial,
of degree strictly below n, even with repeated physical abscissae and n=0. -/
theorem exists_head_poly {n : ℕ} (hx : x ∈ chain (diag c) U w n) :
    ∃ u∈U, ∃ P : Polynomial K, P.degree < (n:ℕ) ∧
      (∀ i, x i = u i+P.eval (c i)*w i) := by
  induction n generalizing x with
  | zero =>
    refine ⟨x,hx,0,?_,?_⟩
    · simp
    · intro i; simp
  | succ n ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u,hu,P,hdeg,he⟩ := ih ha
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨u,hu,P+Polynomial.monomial n t,?_,?_⟩
    · apply lt_of_le_of_lt (Polynomial.degree_add_le ..)
      have lt : (n : WithBot ℕ) < ((n+1:ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self n
      exact max_lt (hdeg.trans lt) ((Polynomial.degree_monomial_le _ _).trans_lt lt)
    · intro i
      rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pow_diag_apply,he i,
        Polynomial.eval_add,Polynomial.eval_monomial]
      ring

theorem nonzero_fiber {z : K} (hz : z∈headSites c w) : fiber c z w ≠ 0 := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  have hn := (Finset.mem_filter.mp hi).2
  intro h
  apply hn
  simpa [fiber] using congrFun h i

/-- A numerical vector supported on just one numerical site cannot come from
a genuine head of insufficient degree; it belongs to the true invariant core.
This is a polynomial root count, not orthogonal projection. -/
theorem localized_mem {n : ℕ} {z : K} (hU : U.map (diag c)≤U)
    (normalized : ∀ a, fiber c a w∈U → fiber c a w=0) (count : n<(headSites c w).card)
    (hx : x∈chain (diag c) U w n) (loc : ∀ i, c i≠z → x i=0) : x∈U := by
  classical
  obtain ⟨u,hu,P,hd,eqn⟩ := exists_head_poly hx
  let Z := (headSites c w).erase z
  have hc : n ≤ Z.card := le_trans (by omega) (Finset.pred_card_le_card_erase (s:=headSites c w) (a:=z))
  have van (a : K) (ha : a∈Z) : P.eval a=0 := by
    have he := Finset.mem_erase.mp ha
    have eqv : P.eval a • fiber c a w = -fiber c a u := by
      ext i
      by_cases e : c i=a
      · have hloc := loc i (e ▸ he.1)
        have hh := eqn i
        rw [hloc,e] at hh
        simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul,fiber,e,ite_true]
        exact eq_neg_of_add_eq_zero_right hh.symm
      · simp [fiber,e]
    by_contra h
    apply nonzero_fiber he.2 (normalized a _)
    apply (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr h)).mp
    rw [eqv]
    exact U.neg_mem (fiber_mem hU a hu)
  have hz : P=0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero Z
    (hd.trans_le (by exact_mod_cast hc)) van
  have he : x=u := by
    ext i
    simpa only [hz,Polynomial.eval_zero,zero_mul,add_zero] using eqn i
  rwa [he]


/-- Decomposition over numerical sites, with all duplicate physical rows
combined in the same head fiber. -/
theorem sum_fibers (c v : Vec K s) : (∑ z ∈ sites c, fiber c z v) = v := by
  classical
  ext i
  rw [Finset.sum_apply,Finset.sum_eq_single_of_mem (c i) (site_mem c i)]
  · simp [fiber]
  · intro z _ hz
    simp [fiber,Ne.symm hz]

/-- Native graded consequence needed in the one-escape chart: whenever an
actual product grade is covered by a sufficiently long normalized chain,
every lower-grade partner preserves the invariant part, without positivity,
genericity of nodes or a prior coordinatewise subalgebra hypothesis. -/
theorem core_mul {A : Fin s → Fin s → K} {j k n : ℕ}
    (hU : U.map (diag (nodes A))≤U) (hi : U≤zeroSpace A j)
    (normalized : ∀ a, fiber (nodes A) a w∈U → fiber (nodes A) a w=0)
    (count : n<(headSites (nodes A) w).card)
    (band : zeroSpace A (j+k) ≤ chain (diag (nodes A)) U w n)
    {u v : Vec K s} (hu : u∈U) (hv : v∈zeroSpace A k) : u*v∈U := by
  classical
  have eqn : u*v=∑ z ∈ sites (nodes A), fiber (nodes A) z u*v := by
    rw [←Finset.sum_mul,sum_fibers]
  rw [eqn]
  apply U.sum_mem
  intro z _
  apply localized_mem (z:=z) hU normalized count (band (zeroSpace_mul (hi (fiber_mem hU z hu)) hv))
  intro i hin
  simp [fiber,hin]


/-- A unit rank budget plus a genuine C-escape covers the entire actual
next grade: it is exactly the cost of adjoining one clock image. -/
theorem ordinary_step {A : Fin s → Fin s → K} {j : ℕ}
    (one : finrank K (zeroSpace A (j+1)) ≤ finrank K (zeroSpace A j)+1)
    (out : ¬(zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) :
    zeroSpace A (j+1)=zeroSpace A j ⊔ (zeroSpace A j).map (diag (nodes A)) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le (zeroSpace_mono A (by omega)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j))
  · have lt : zeroSpace A j < zeroSpace A j ⊔ (zeroSpace A j).map (diag (nodes A)) :=
      lt_of_le_of_ne le_sup_left (fun e => out (le_sup_right.trans (le_of_eq e.symm)))
    have h := Submodule.finrank_lt_finrank_of_lt lt
    omega

/-- Each consecutive unit, noninvariant step of the true RK flag extends the
same normalized head by another clock power; no new generator may appear. -/
theorem ordinary_staircase {A : Fin s → Fin s → K} {j h r : ℕ}
    (hU : U.map (diag (nodes A))≤U) (pos : 0<r)
    (base : zeroSpace A j=chain (diag (nodes A)) U w r)
    (one : ∀ k<h, finrank K (zeroSpace A (j+k+1))≤finrank K (zeroSpace A (j+k))+1)
    (out : ∀ k<h, ¬(zeroSpace A (j+k)).map (diag (nodes A)) ≤ zeroSpace A (j+k)) :
    ∀ k≤h, zeroSpace A (j+k) = chain (diag (nodes A)) U w (r+k) := by
  intro k hk
  induction k with
  | zero => simpa only [Nat.add_zero] using base
  | succ k ih =>
    rw [show j+(k+1)=j+k+1 by omega,ordinary_step (one k (by omega)) (out k (by omega)),ih (by omega)]
    exact chain_sup_map hU (by omega)

end RKCert.Paired.Clock
