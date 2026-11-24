module
public import RKCert.OneEscape
public import RKCert.ForwardDefects
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section
namespace RKCert.OneEscape
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {T : V →ₗ[K] V} {U S : Submodule K V} {w u : V}
theorem pow_mem (hU : U.map T ≤ U) {v : V} (hv : v∈U) (k : ℕ) : (T^k) v∈U := by
  induction k with
  | zero => simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using hv
  | succ k ih => rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]; exact hU ⟨_,ih,rfl⟩

theorem chain_le_iff (n : ℕ) : chain T U w n ≤ S ↔ U≤S ∧ ∀ k<n,(T^k) w∈S := by
  induction n with
  | zero => simp only [chain,Nat.not_lt_zero,IsEmpty.forall_iff,implies_true,and_true]
  | succ n ih =>
    rw [chain,sup_le_iff,ih,Submodule.span_singleton_le_iff_mem]
    constructor
    · rintro ⟨⟨hU,hk⟩,hn⟩
      refine ⟨hU,fun k hh => ?_⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hh) with rfl|ha
      · exact hn
      · exact hk k ha
    · rintro ⟨hU,hk⟩
      exact ⟨⟨hU,fun k hh=>hk k (by omega)⟩,hk _ (by omega)⟩

theorem chain_sub_head (hU : U.map T≤U) (hu : u∈U) (n : ℕ) :
    chain T U (w-u) n = chain T U w n := by
  have h1 := (chain_le_iff (T:=T) (U:=U) (w:=w) n).mp le_rfl
  have h2 := (chain_le_iff (T:=T) (U:=U) (w:=w-u) n).mp le_rfl
  apply le_antisymm
  · apply (chain_le_iff _).mpr
    refine ⟨h1.1,fun k hk => ?_⟩
    rw [map_sub]
    exact (chain T U w n).sub_mem (h1.2 _ hk) (h1.1 (pow_mem hU hu _))
  · apply (chain_le_iff _).mpr
    refine ⟨h2.1,fun k hk => ?_⟩
    have hh := (chain T U (w-u) n).add_mem (h2.2 _ hk) (h2.1 (pow_mem hU hu k))
    simpa only [map_sub,sub_add_cancel] using hh
end RKCert.OneEscape

namespace RKCert.Paired.Clock
open RKCert.Paired RKCert.OneEscape Module
variable {K : Type*} [Field K] {s : ℕ}
variable {c : Vec K s} {A : Fin s → Fin s → K}
theorem pow_diag_apply (c v : Vec K s) (k : ℕ) (i : Fin s) : (diag c ^ k) v i = c i^k*v i := by
  induction k with
  | zero => simp only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply,one_mul]
  | succ k ih => rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply,diag_apply,ih,pow_succ]; ring

/-- Each true clock-stable part decomposes over actual numerical abscissae,
even when physically different stages have the same abscissa. -/
noncomputable def fiber (c : Vec K s) (z : K) (v : Vec K s) : Vec K s :=
  by classical exact fun i => if c i = z then v i else 0

noncomputable def sites (c : Vec K s) : Finset K := by classical exact Finset.univ.image c
omit [Field K] in
theorem site_mem (c : Vec K s) (i : Fin s) : c i ∈ sites c := by
  classical exact Finset.mem_image_of_mem c (Finset.mem_univ _)

theorem poly_preserves {U : Submodule K (Vec K s)} (hU : U.map (diag c) ≤ U)
    (P : Polynomial K) (v : Vec K s) (h : v∈U) :
    (fun i => P.eval (c i)*v i) ∈ U := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add,add_mul,Pi.add_def] using U.add_mem hp hq
  | monomial n a =>
    have hp (k : ℕ) : (diag c^k) v ∈ U := by
      induction k with
      | zero => simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h
      | succ k ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
        exact hU ⟨_,ih,rfl⟩
    have hs := U.smul_mem a (hp n)
    convert hs using 1
    ext i
    simp only [Polynomial.eval_monomial,Pi.smul_apply,smul_eq_mul,pow_diag_apply]
    ring

theorem fiber_mem {U : Submodule K (Vec K s)} (hU : U.map (diag c) ≤ U)
    (z : K) {v : Vec K s} (h : v∈U) : fiber c z v∈U := by
  classical
  by_cases hz : z ∈ sites c
  · let P := Lagrange.basis (sites c) id z
    have eqn : fiber c z v = fun i => P.eval (c i)*v i := by
      ext i
      by_cases e : c i=z
      · have hj := @Lagrange.eval_basis_self K _ K _ (sites c) id z (Set.injOn_id _) hz
        change (if c i=z then v i else 0) = P.eval (c i)*v i
        simp only [e,ite_true]
        rw [show P.eval z = 1 from hj,one_mul]
      · have hj := @Lagrange.eval_basis_of_ne K _ K _ (sites c) id z (c i) (Ne.symm e) (site_mem c i)
        change (if c i=z then v i else 0) = P.eval (c i)*v i
        simp only [e,ite_false]
        rw [show P.eval (c i)=0 from hj,zero_mul]
    rw [eqn]
    exact poly_preserves hU P v h
  · have hh : fiber c z v=0 := by
      ext i
      have he : c i≠z := fun e => hz (e ▸ site_mem c i)
      simp [fiber,he]
    rw [hh]; exact U.zero_mem


/-- Componentwise subtraction of exactly those head components already in U. -/
noncomputable def correction (c : Vec K s) (U : Submodule K (Vec K s)) (w : Vec K s) : Vec K s := by
  classical exact ∑ z ∈ (sites c).filter (fun z => fiber c z w∈U), fiber c z w

theorem correction_mem (c : Vec K s) (U : Submodule K (Vec K s)) (w : Vec K s) :
    correction c U w ∈ U := by
  classical
  exact U.sum_mem (fun z hz => (Finset.mem_filter.mp hz).2)

theorem correction_apply (c : Vec K s) (U : Submodule K (Vec K s)) (w : Vec K s)
    (i : Fin s) : correction c U w i = (by classical exact if fiber c (c i) w∈U then w i else 0) := by
  classical
  unfold correction
  rw [Finset.sum_apply]
  by_cases h : fiber c (c i) w ∈ U
  · simp only [h,ite_true]
    rw [Finset.sum_eq_single_of_mem (c i) (Finset.mem_filter.mpr ⟨site_mem c i,h⟩)]
    · simp [fiber]
    · intro z _ hz
      simp [fiber,Ne.symm hz]
  · simp only [h,ite_false]
    apply Finset.sum_eq_zero
    intro z hz
    have he : c i≠z := by
      rintro rfl
      exact h (Finset.mem_filter.mp hz).2
    simp [fiber,he]

theorem normalized (c : Vec K s) (U : Submodule K (Vec K s)) (w : Vec K s) (z : K)
    (hm : fiber c z (w-correction c U w) ∈ U) : fiber c z (w-correction c U w) = 0 := by
  classical
  by_cases h : fiber c z w ∈ U
  · ext i
    by_cases e : c i = z
    · simp [fiber,e,Pi.sub_apply,correction_apply,h]
    · simp [fiber,e]
  · exfalso
    apply h
    have eqn : fiber c z (w-correction c U w)=fiber c z w := by
      ext i
      by_cases e : c i=z
      · simp [fiber,e,Pi.sub_apply,correction_apply,h]
      · simp [fiber,e]
    rwa [←eqn]


/-- Distinct *numerical* clock sites of a column, not physical stage count. -/
noncomputable def headSites (c w : Vec K s) : Finset K := by
  classical exact (Finset.univ.filter fun i => w i ≠ 0).image c

theorem headSites_mem {w : Vec K s} (i : Fin s) (hi : w i ≠ 0) : c i ∈ headSites c w := by
  classical exact Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

/-- Pinned Mathlib interpolation converts the first unpayable diagonal iterate
into a strict lower bound on the number of different nonzero head fibers. -/
theorem more_sites_than_paid {w : Vec K s} {r : ℕ} {F : Submodule K (Vec K s)}
    (paid : ∀ j<r, (diag c^j) w∈F) (out : (diag c^r) w∉F) : r < (headSites c w).card := by
  classical
  by_contra! le
  let Z := headSites c w
  let P := Lagrange.interpolate Z id (fun z => z^r)
  have ev : (diag c^r) w = fun i => P.eval (c i)*w i := by
    ext i
    rw [pow_diag_apply]
    by_cases h : w i=0
    · simp [h]
    · have hz : c i∈Z := headSites_mem i h
      have he : P.eval (c i) = (c i)^r :=
        Lagrange.eval_interpolate_at_node (fun z:K => z^r) (Set.injOn_id _) hz
      rw [he]
  apply out
  rw [ev]
  by_cases hp : P=0
  · have he : (fun i : Fin s => P.eval (c i)*w i) = (0 : Vec K s) := by ext i; simp [hp]
    rw [he]
    exact F.zero_mem
  have deg : P.natDegree < Z.card := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
    (Lagrange.degree_interpolate_lt (fun z:K => z^r) (Set.injOn_id _))
  have e : (fun i => P.eval (c i)*w i) = ∑ j ∈ Finset.range Z.card, P.coeff j • (diag c ^j) w := by
    ext i
    rw [Finset.sum_apply,Polynomial.eval_eq_sum_range' deg,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply,smul_eq_mul,pow_diag_apply,mul_assoc]
  rw [e]
  exact F.sum_mem (fun j hj => F.smul_mem _ (paid j ((Finset.mem_range.mp hj).trans_le le)))

/-- The one-escape hypothesis is inferred from a one-stage rank budget in the
actual rooted-tree defect filtration, not supplied on F+CF. -/
theorem ordinary_single_head (A : Fin s → Fin s → K) (j : ℕ)
    (one : finrank K (zeroSpace A (j+1)) ≤ finrank K (zeroSpace A j)+1)
    (out : ¬ (zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) :
    ∃ (r : ℕ) (U : Submodule K (Vec K s)) (w : Vec K s),
      0<r ∧ U.map (diag (nodes A)) ≤ U ∧ U ≤ zeroSpace A j ∧
      (∀ S : Submodule K (Vec K s), S.map (diag (nodes A)) ≤ S → S≤zeroSpace A j → S≤U) ∧
      zeroSpace A j=chain (diag (nodes A)) U w r ∧
      (∀ k<r,(diag (nodes A)^k) w∈zeroSpace A j) ∧
      (diag (nodes A)^r) w∉zeroSpace A j ∧ finrank K (zeroSpace A j)=finrank K U+r := by
  apply single_head _ out
  apply le_trans _ one
  apply Submodule.finrank_mono
  exact sup_le (zeroSpace_mono A (by omega)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j))


/-- Chart-native, normalized one-head representation. Every active fiber is
genuinely outside the largest invariant subspace, and its distinct numerical
sites strictly outnumber the powers already paid for by the true grade. -/
theorem ordinary_normal_head (A : Fin s → Fin s → K) (j : ℕ)
    (one : finrank K (zeroSpace A (j+1)) ≤ finrank K (zeroSpace A j)+1)
    (out : ¬ (zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) :
    ∃ (r : ℕ) (U : Submodule K (Vec K s)) (v : Vec K s),
      0<r ∧ U.map (diag (nodes A)) ≤ U ∧ U ≤ zeroSpace A j ∧
      (∀ S : Submodule K (Vec K s), S.map (diag (nodes A)) ≤ S → S≤zeroSpace A j → S≤U) ∧
      zeroSpace A j=chain (diag (nodes A)) U v r ∧
      (∀ k<r,(diag (nodes A)^k) v∈zeroSpace A j) ∧
      (diag (nodes A)^r) v∉zeroSpace A j ∧ finrank K (zeroSpace A j)=finrank K U+r ∧
      (∀ z, fiber (nodes A) z v∈U → fiber (nodes A) z v=0) ∧
      r<(headSites (nodes A) v).card := by
  obtain ⟨r,U,w,pos,hU,hin,largest,spans,paid,escape,hd⟩ := ordinary_single_head A j one out
  let u := correction (nodes A) U w
  have hu : u∈U := correction_mem _ _ _
  have hu' (k : ℕ) : (diag (nodes A)^k) u∈zeroSpace A j := hin (pow_mem hU hu _)
  have hpaid (k : ℕ) (hk : k<r) : (diag (nodes A)^k) (w-u) ∈ zeroSpace A j := by
    rw [map_sub]
    exact (zeroSpace A j).sub_mem (paid k hk) (hu' k)
  have hout : (diag (nodes A)^r) (w-u) ∉ zeroSpace A j := by
    intro h
    have he := (zeroSpace A j).add_mem h (hu' r)
    apply escape
    simpa only [map_sub,sub_add_cancel] using he
  exact ⟨r,U,w-u,pos,hU,hin,largest,spans.trans (chain_sub_head hU hu _).symm,hpaid,hout,hd,
    normalized (nodes A) U w, more_sites_than_paid hpaid hout⟩

end RKCert.Paired.Clock
