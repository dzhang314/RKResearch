module
public import RKCert.DirkEvenJointSupport
@[expose] public section
namespace RKCert.OneEscape
open Module
variable {K V:Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The largest invariant subspace of an arbitrary finite-dimensional
subspace. No clock diagonality is needed for existence or maximality. -/
theorem largest_invariant (T:V→ₗ[K]V) (F:Submodule K V) :
    ∃U:Submodule K V,U≤F ∧ U.map T≤U ∧ ∀W:Submodule K V,W≤F → W.map T≤W → W≤U := by
  obtain ⟨n,_,h⟩:=exists_plateau T F
  refine ⟨core T F n,?_,invariant_of_plateau h,fun W hw hi=>invariant_le_core hw hi n⟩
  intro x hx
  simpa using mem_core.mp hx 0 (Nat.zero_le _)

/-- Any flag piece not contained in the terminal invariant core increases
its summed dimension at every subsequent clock step up to the horizon. -/
theorem terminal_quotient_growth (T:V→ₗ[K]V) (F:ℕ→Submodule K V) {m j:ℕ}
    (mono:Monotone F) (hstep:∀k,(F k).map T≤F (k+1))
    {U:Submodule K V} (hU:U≤F m) (hi:U.map T≤U)
    (largest:∀W:Submodule K V,W≤F m → W.map T≤W → W≤U)
    (hj:j≤m) (outside:¬F j≤U) :
    finrank K (F j ⊔ U : Submodule K V)+(m-j)≤finrank K (F m) := by
  let G (l:ℕ):Submodule K V:=F l ⊔ U
  have hmono:Monotone G:=fun _ _ le=>sup_le_sup_right (mono le) U
  have out (l:ℕ) (jl:j≤l) (lm:l≤m):¬(G l).map T≤G l := by
    intro inv
    exact outside ((mono jl).trans (le_sup_left.trans (largest _ (sup_le (mono lm) hU) inv)))
  have gain (r:ℕ) (hr:j+r≤m) : finrank K (G j)+r≤finrank K (G (j+r)) := by
    induction r with
    | zero=>simp
    | succ r ih=>
      have before:=ih (by omega)
      have step:G (j+r)<G (j+r+1):=lt_of_le_of_ne (hmono (by omega)) (fun eqn=>out (j+r) (by omega) (by omega) (by
        calc
          (G (j+r)).map T ≤ G (j+r+1) := by
            change ((F (j+r) ⊔ U : Submodule K V).map T)≤F (j+r+1) ⊔ U
            rw [Submodule.map_sup]
            exact sup_le ((hstep _).trans le_sup_left) (hi.trans le_sup_right)
          _ = G (j+r) := eqn.symm))
      have rank:=Submodule.finrank_lt_finrank_of_lt step
      change _≤finrank K (G (j+r+1))
      omega
  have g:=gain (m-j) (by omega)
  rw [show j+(m-j)=m by omega] at g
  rw [show G m=F m from sup_eq_left.mpr hU] at g
  exact g
end RKCert.OneEscape

namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem even_core_three (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    ∃U:Submodule K (Vec K (s+1)),U≤zeroSpace A m ∧ U.map (diag (nodes A))≤U ∧
      (∀W:Submodule K (Vec K (s+1)),W≤zeroSpace A m → W.map (diag (nodes A))≤W → W≤U) ∧
      finrank K U≤3 := by
  let F:=zeroSpace A
  let T:=diag (nodes A)
  obtain ⟨U,um,ui,largest⟩:=largest_invariant T (F m)
  refine ⟨U,um,ui,largest,?_⟩
  let k:=finrank K U
  obtain ⟨_,r3,_,rprev,rm,_⟩:=even_boundary hm ha ho he
  change finrank K (F 3)=1 at r3
  change finrank K (F (m-1))=m-2 at rprev
  change finrank K (F m)=m-1 at rm
  have step (j:ℕ):(F j).map T≤F (j+1):=Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)
  have mono:Monotone F:=fun _ _ h=>zeroSpace_mono A h
  have quota (j:ℕ) (hj:j≤m) (out:¬F j≤U) :
      finrank K (F j ⊔ U :Submodule K (Vec K (s+1)))+(m-j)≤m-1 := by
    rw [←rm]; exact terminal_quotient_growth T F mono step um ui largest hj out
  have fin (j:ℕ) (jl:2≤j) (jm:j≤m):finrank K (F j)≤j-1 := by
    have hh:=flag_gain ha ho (a:=j) (n:=m) jl jm (by omega)
    change finrank K (F j)+(m-j)≤finrank K (F m) at hh
    omega
  have low (j:ℕ) (jl:3≤j) (jm:j≤m):j-2≤finrank K (F j) := by
    have hh:=flag_gain ha ho (a:=3) (n:=j) (by decide) jl (by omega)
    change finrank K (F 3)+(j-3)≤finrank K (F j) at hh
    omega
  have inc:(F m).map T≤F m → False := by
    intro ii
    have rg:=dirk_forward_invariant_incoming ha ho (j:=m) (by omega) (fun v hv=>ii ⟨v,hv,rfl⟩)
    change finrank K (F (m-1))+(m-1)/2≤finrank K (F m) at rg
    omega
  have kpre:k<m-1:=by
    have strict:U<F m:=lt_of_le_of_ne um (fun eqn=>inc (eqn ▸ ui))
    have rg:=Submodule.finrank_lt_finrank_of_lt strict
    dsimp [k];omega
  have init:F (k+1)≤U:=by
    by_contra out
    have rank:=quota _ (by omega) out
    have strict:U<F (k+1) ⊔ U:=lt_of_le_of_ne le_sup_right (fun eqn=>out (le_sup_left.trans (le_of_eq eqn.symm)))
    have rg:=Submodule.finrank_lt_finrank_of_lt strict
    change k<_ at rg
    omega
  have room:k+3≤m:=by
    by_contra! short
    have eqn:k+1=m-1:=by omega
    rw [eqn] at init
    have f: F (m-1)=U:=Submodule.eq_of_le_of_finrank_le init (by change k≤_;omega)
    have inside:(F (m-1)).map T≤F (m-1):=f ▸ ui
    have rg:=dirk_forward_invariant_outgoing ha ho (j:=m-1) (by omega) (F (m-1)) le_rfl
      (fun v hv=>inside ⟨v,hv,rfl⟩)
    change finrank K (F (m-1))+(m-1)/2≤finrank K (F (m-1+1)) at rg
    rw [show m-1+1=m by omega] at rg
    omega
  change k≤3
  by_contra! high
  have ini:finrank K (F (k+1))≤k:=Submodule.finrank_mono init
  have below:=low (k+1) (by omega) (by omega)
  have next:U≤F (k+2) := by
    by_cases eqn:finrank K (F (k+1))=k
    · rw [←Submodule.eq_of_le_of_finrank_le init (by change k≤_;omega)]
      exact mono (by omega)
    by_cases inv:(F (k+1)).map T≤F (k+1)
    · have grown:=dirk_forward_invariant_outgoing ha ho (j:=k+1) (by omega) (F (k+1)) le_rfl
        (fun v hv=>inv ⟨v,hv,rfl⟩)
      change finrank K (F (k+1))+(k+1)/2≤finrank K (F (k+2)) at grown
      have rg:k+1≤finrank K (F (k+2)):=by omega
      have out:¬F (k+2)≤U:=fun e=>by have h:finrank K (F (k+2))≤k:=Submodule.finrank_mono e;omega
      have bound:=quota _ (by omega) out
      have eqn':F (k+2)=F (k+2) ⊔ U:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
      exact le_sup_right.trans (le_of_eq eqn'.symm)
    · let W:=F (k+1) ⊔ (F (k+1)).map T
      have inU:W≤U:=sup_le init ((Submodule.map_mono init).trans ui)
      have strict:F (k+1)<W:=lt_of_le_of_ne le_sup_left
        (fun e=>inv (le_sup_right.trans (le_of_eq e.symm)))
      have bigger:=Submodule.finrank_lt_finrank_of_lt strict
      have eqn':W=U:=Submodule.eq_of_le_of_finrank_le inU (by change k≤_;omega)
      exact eqn' ▸ sup_le (mono (by omega)) (step _)
  have grown:=dirk_forward_invariant_outgoing ha ho (j:=k+2) (by omega) U next (fun v hv=>ui ⟨v,hv,rfl⟩)
  change k+(k+2)/2≤finrank K (F (k+3)) at grown
  have bound:=fin (k+3) (by omega) room
  omega
end RKCert.Paired.Terminal
