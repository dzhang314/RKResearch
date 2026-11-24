module

public import RKCert.ReviewedNative.ERKOrder15GradeTen
public import RKCert.ReviewedNative.ClockHeadSupport

@[expose] public section

/-! # The actual order-15 physical core is a coordinate algebra
Localize a product on each true clock fibre, apply grade-ten separation,
then reuse the existing tree-independent head localization. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a r : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

private theorem coordinate_mul {t : Fin (s+1)} (v : Fin (s+1)→K) :
    coordinate t * v = v t • coordinate t := by
  ext i
  by_cases e : i=t
  · subst i
    simp [coordinate]
  · simp [coordinate,e]

private theorem terminalMark_mul {x y : Fin (s+1)→K} (h : x∈terminalMark A b) :
    x*y∈terminalMark A b := by
  by_cases z : firstSeed A b=0
  · rw [terminalMark,ite_eq_left z] at h ⊢
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [smul_mul_assoc,coordinate_mul]
    exact (K ∙ coordinate (Fin.last s)).smul_mem _ ((K ∙ coordinate (Fin.last s)).smul_mem _
      (Submodule.mem_span_singleton_self _))
  · rw [terminalMark,ite_eq_right z] at h ⊢
    rw [(Submodule.mem_bot K).mp h,zero_mul]
    exact (⊥ : Submodule K (Fin (s+1)→K)).zero_mem

/-- Marking the real last coordinate respects the graded product,
since its entire line is a coordinatewise ideal. -/
theorem marked_defect_mul {j k : ℕ} {x y : Fin (s+1)→K}
    (hx : x∈markedDefectSpace A b j) (hy : y∈markedDefectSpace A b k) :
    x*y∈markedDefectSpace A b (j+k) := by
  obtain ⟨u,hu,t,ht,rfl⟩:=Submodule.mem_sup.mp hx
  obtain ⟨v,hv,z,hz,rfl⟩:=Submodule.mem_sup.mp hy
  rw [show (u+t)*(v+z)=u*v+(z*u+t*(v+z)) by ring]
  exact Submodule.mem_sup.mpr ⟨_,zeroSpace_mul hu hv,_,
    (terminalMark A b).add_mem (terminalMark_mul hz) (terminalMark_mul ht),rfl⟩

/-- At least this many distinct clock fibres are still genuinely outside
the invariant core. Repeated numerical nodes and live core fibres are
not counted again. -/
theorem Order15PaidStaircase.ten_has_escape_sites (S : Order15PaidStaircase A b a G r U w)
    (ho : HasOrder A b 15) :
    order15HeadLength a r 10 < (HeadFiber.escapeSites (nodes A) w U).card := by
  have aa := S.base_degree
  have rank11 := (S.band_direct_rank ho (j:=11) (by omega) (by decide)).2
  have rank12 := (S.band_direct_rank ho (j:=12) (by omega) (by decide)).2
  have len : order15HeadLength a r 12=order15HeadLength a r 11+1 := by
    unfold order15HeadLength
    omega
  have non : ¬ (order15HeadBand A a r 11 U w).map (diag (nodes A))≤order15HeadBand A a r 11 U w := by
    intro iv
    have e := (S.band_next (j:=11) (by omega)).symm.trans (sup_eq_left.mpr iv)
    rw [e,rank11,len] at rank12
    omega
  have enough := HeadFiber.more_escape_sites S.stable
    (by unfold order15HeadLength;omega : 0<order15HeadLength a r 11) non
  unfold order15HeadLength at enough ⊢
  omega

/-- Actual grade-five physical defects preserve the entire invariant
head core under coordinatewise multiplication. -/
theorem Order15PaidStaircase.core_times_five (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder A b 15)
    {v u : Fin (s+1)→K} (hv : v∈markedDefectSpace A b 5) (hu : u∈U) : u*v∈U := by
  let c := nodes A
  let D := diag c
  have stable (x : Fin (s+1)→K) (hx : x∈U) : D x∈U :=
    S.stable (Submodule.mem_map_of_mem hx)
  have mask := clock_mask_invariant stable
  let f (z : K) := blockMask c z u * v
  have each (z : K) : f z∈U := by
    have clocks (i : ℕ) : (D^i) (blockMask c z u)∈U := by
      induction i with
      | zero => simpa using mask z u hu
      | succ i ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
        exact stable _ ih
    have pays (i : ℕ) (_ : i≤2+terminalDebit A b) : (D^i) (f z)∈markedDefectSpace A b 10 := by
      have eq : (D^i) (f z)=((D^i) (blockMask c z u))*v := by
        ext j
        simp [D,f,mul_assoc]
      rw [eq]
      exact marked_defect_mul (j:=5) (k:=5) (S.earlyCore (clocks i)) hv
    have paid := S.ten_leak_free ha ho pays
    apply HeadFiber.localized_mem S.stable (S.ten_has_escape_sites ho) paid (z:=z)
    intro i hi
    simp [f,blockMask,c,hi]
  have e : assembleBlocks c f=u*v := by ext i; simp [f,blockMask]
  exact e ▸ assembleBlocks_mem c mask f each

/-- The original chart admits the same head supported away from every
actual live coordinate of its multiplicatively closed core. -/
theorem Order15PaidStaircase.clean_head (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder A b 15) :
    ∃ v : Fin (s+1)→K, Order15PaidStaircase A b a G r U v ∧
      (∀ i, (∃ u∈U, u i≠0) → v i=0) ∧ (∀ u∈U,∀ z∈U,u*z∈U) := by
  have closed (u : Fin (s+1)→K) (hu : u∈U) (z : Fin (s+1)→K) (hz : z∈U) : u*z∈U :=
    S.core_times_five ha ho (S.earlyCore hz) hu
  have w5 : w∈markedDefectSpace A b 5 := by
    have edge := S.early 0 (by decide)
    change markedDefectSpace A b 5=chain (diag (nodes A)) U w r at edge
    rw [edge]
    have e := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) r).mp le_rfl
    simpa using e.2 0 (by have := S.headLength;omega)
  obtain ⟨v,dis,e⟩ := HeadFiber.disjoint_rep S.stable closed
    (fun _ h=>S.core_times_five ha ho w5 h)
  refine ⟨v,⟨S.frame,S.first,S.headLength,S.headRank,S.stable,S.earlyCore,?_,?_,?_⟩,dis,closed⟩
  · intro n hn
    rw [e]
    exact S.early n hn
  · rw [e]
    exact S.escape
  · intro j hj hmax
    rw [e]
    exact S.full j hj hmax

end
end RKResearch.Certified.Graded
