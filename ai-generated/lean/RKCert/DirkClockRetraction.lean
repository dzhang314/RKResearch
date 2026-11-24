module

public import RKCert.ChronologicalPivotProjection

@[expose] public section

/-! # Clockwise chronological projection of an arbitrary invariant core

The eliminated vector at each step is local at the earliest surviving
physical pivot. The final map remains triangular and respects the actual
clock; the construction requires no coordinatewise multiplication
closure of the eliminated subspace. All stages remain as padded slots.
-/
namespace RKCert.Paired.PivotProjection
open RKCert.Endpoint RKCert.OneEscape Module Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}

structure ClockRetraction (c : Vec K s) (U : Submodule K (Vec K s)) where
  projection : Vec K s →ₗ[K] Vec K s
  diagonal : Vec K s
  causal : CausalDiag (Equiv.refl (Fin s)) projection diagonal
  kills : ∀ x∈U,projection x=0
  defect : ∀ x,x-projection x∈U
  clock : ∀ x,projection (diag c x)=diag c (projection x)
  weighted : ∀ x P,projection (weightedEval c x P)=weightedEval c (projection x) P

theorem exists_clock_retraction (c : Vec K s) (U : Submodule K (Vec K s))
    (inv : U.map (diag c)≤U) : Nonempty (ClockRetraction c U) := by
  classical
  have go (n : ℕ) : ∀ U : Submodule K (Vec K s), finrank K U=n →
      U.map (diag c)≤U → Nonempty (ClockRetraction c U) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U dim inv
      by_cases e : U=⊥
      · subst U
        refine ⟨⟨LinearMap.id,1,?_,?_,?_ ,?_,?_⟩⟩
        · intro i v _
          simp
        · intro x hx
          simpa only [LinearMap.id_apply,Submodule.mem_bot] using hx
        · intro x
          simp
        · intro x
          rfl
        · intro x P
          rfl
      let L := Finset.univ.filter (Clock.Live U)
      have neL : L.Nonempty := by
        by_contra nL
        apply e
        apply bot_unique
        intro x hx
        rw [Submodule.mem_bot]
        funext i
        change x i=0
        by_contra nz
        exact nL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,hx,nz⟩⟩⟩
      let i := L.min' neL
      obtain ⟨u,hu,ui⟩ := (Finset.mem_filter.mp (L.min'_mem neL)).2
      let d := Clock.fiber c (c i) u
      have hd : d∈U := Clock.fiber_mem inv (c i) hu
      have di : d i≠0 := by simpa [d,Clock.fiber] using ui
      have loc (j : Fin s) (hj : c j≠c i) : d j=0 := by simp [d,Clock.fiber,hj]
      have pref (j : Fin s) (hj : j < i) : d j=0 := by
        by_contra hz
        have jl : j∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨d,hd,hz⟩⟩
        exact (not_le_of_gt hj) (L.min'_le j jl)
      let V := U ⊓ LinearMap.ker (LinearMap.proj i)
      have vu : V≤U := inf_le_left
      have strict : V<U := lt_of_le_of_ne vu (fun e => by
        have hv : d∈V := by rw [e]; exact hd
        exact di hv.2)
      have low : finrank K V<n := (Submodule.finrank_lt_finrank_of_lt strict).trans_eq dim
      have vInv : V.map (diag c)≤V := by
        rintro _ ⟨x,hx,rfl⟩
        have hzi : x i=0 := hx.2
        refine ⟨inv ⟨x,hx.1,rfl⟩,?_⟩
        change (diag c x) i=0
        simp [hzi]
      obtain ⟨P⟩ := ih _ low V rfl vInv
      let R := remove d i
      let p : Vec K s := fun j => if j=i then 0 else 1
      have hR : (U.map R)≤V := by
        rintro _ ⟨x,hx,rfl⟩
        refine ⟨?_,remove_pivot di x⟩
        change remove d i x∈U
        rw [remove_apply]
        exact U.sub_mem hx (U.smul_mem _ hd)
      refine ⟨⟨P.projection.comp R,P.diagonal*p,causal_comp P.causal
        (remove_causal (ord:=Equiv.refl (Fin s)) di pref),?_,?_,?_,?_⟩⟩
      · intro x hx
        exact P.kills _ (hR ⟨x,hx,rfl⟩)
      · intro x
        change x-P.projection (R x)∈U
        rw [show x-P.projection (R x)=(x-R x)+(R x-P.projection (R x)) by abel]
        apply U.add_mem _ (vu (P.defect _))
        change x-remove d i x∈U
        rw [remove_apply,sub_sub_cancel]
        exact U.smul_mem _ hd
      · intro x
        change P.projection (remove d i (diag c x))=diag c (P.projection (remove d i x))
        rw [remove_clock loc,P.clock]
      · intro x Q
        change P.projection (remove d i (weightedEval c x Q))=
          weightedEval c (P.projection (remove d i x)) Q
        rw [remove_weighted loc,P.weighted]
  exact go _ U rfl inv

namespace ClockRetraction
variable {c : Vec K s} {U : Submodule K (Vec K s)}
variable (P : ClockRetraction c U)

theorem idempotent (x : Vec K s) : P.projection (P.projection x)=P.projection x := by
  have e := P.kills _ (P.defect x)
  rw [map_sub,sub_eq_zero] at e
  exact e.symm

theorem preserve_functional (f : Vec K s →ₗ[K] K)
    (h : ∀ x∈U,f x=0) (x : Vec K s) : f (P.projection x)=f x := by
  have e := h _ (P.defect x)
  rw [map_sub,sub_eq_zero] at e
  exact e.symm

theorem map_chain (w : Vec K s) (n : ℕ) :
    (chain (diag c) U w n).map P.projection=chain (diag c) ⊥ (P.projection w) n := by
  have powClock (r : ℕ) :
      P.projection ((diag c^r) w)=(diag c^r) (P.projection w) := by
    induction r with
    | zero => simp
    | succ r ih =>
      simp only [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      rw [P.clock,ih]
  have killU : U.map P.projection=⊥ := by
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    rw [Submodule.mem_bot]
    exact P.kills _ hx
  induction n with
  | zero => exact killU
  | succ n ih => rw [chain,Submodule.map_sup,ih,Submodule.map_span,Set.image_singleton,powClock,chain]

end ClockRetraction
end
end RKCert.Paired.PivotProjection
