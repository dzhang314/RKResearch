module

public import RKCert.Dirk15MinimalK2Core
public import RKCert.Dirk15GhostPositions
public import RKCert.Dirk15FiberSurjectivity

@[expose] public section

/-! # At most one joint-signature block can carry a non-ghost core column -/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]
variable {A : Fin 20→Fin 20→K} {b v : Vec K 20}

def noGhostEntries (A : Fin 20→Fin 20→K) (b : Vec K 20) : Submodule K (Vec K 20) :=
  ⨅ (i : Fin 20) (_ : i∈ghostPositions A b), LinearMap.ker (LinearMap.proj i)

theorem mem_noGhostEntries {w : Vec K 20} :
    w∈noGhostEntries A b ↔ ∀ i∈ghostPositions A b,w i=0 := by
  simp [noGhostEntries]

theorem ghost_split (U : Submodule K (Vec K 20)) (gU : simultaneousGhosts A b≤U) :
    U=simultaneousGhosts A b⊔(U⊓noGhostEntries A b) ∧
      Disjoint (simultaneousGhosts A b) (U⊓noGhostEntries A b) := by
  let G := simultaneousGhosts A b
  let V := U⊓noGhostEntries A b
  refine ⟨le_antisymm ?_ (sup_le gU inf_le_left),?_⟩
  · intro u hu
    let g : Vec K 20 := fun i=>if i∈ghostPositions A b then u i else 0
    have hg : g∈G := by
      change g∈simultaneousGhosts A b
      rw [simultaneousGhosts_eq_kernels]
      simp only [Submodule.mem_iInf,LinearMap.mem_ker,LinearMap.proj_apply]
      intro i ni
      simp [g,ni]
    have hz : u-g∈V := by
      refine ⟨U.sub_mem hu (gU hg),mem_noGhostEntries.mpr (fun i hi=>?_)⟩
      simp [g,hi]
    exact Submodule.mem_sup.mpr ⟨g,hg,u-g,hz,by abel⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    ext i
    change x i=0
    by_cases g : i∈ghostPositions A b
    · exact mem_noGhostEntries.mp hx.2.2 i g
    · exact ghostPositions_vanish hx.1 g

theorem ghost_residual_diag {U : Submodule K (Vec K 20)} {c : Vec K 20}
    (inv : U.map (diag c)≤U) :
    (U⊓noGhostEntries A b).map (diag c)≤U⊓noGhostEntries A b := by
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨inv (Submodule.mem_map_of_mem hx.1),mem_noGhostEntries.mpr (fun i hi => ?_)⟩
  rw [diag_apply,mem_noGhostEntries.mp hx.2 i hi,mul_zero]

namespace Order15K2Head
variable (h : Order15K2Head A b v)

def residual : Submodule K (Vec K 20) := h.head.U⊓noGhostEntries A b

theorem split : h.head.U=simultaneousGhosts A b⊔h.residual ∧
    Disjoint (simultaneousGhosts A b) h.residual :=
  ghost_split _ h.head.ghosts

theorem rank_split (H : Order15MinimalMarkedChart A b) :
    finrank K (simultaneousGhosts A b)+finrank K h.residual=2 ∧ finrank K h.residual≤1 := by
  have e := Submodule.finrank_sup_add_finrank_inf_eq (simultaneousGhosts A b) h.residual
  rw [←h.split.1,h.split.2.eq_bot,finrank_bot,add_zero,h.core_two] at e
  have f := Submodule.finrank_mono h.head.cubic
  rw [H.initial.f3] at f
  exact ⟨e.symm,by omega⟩

variable [CharZero K]

theorem one_joint_line (D : h.head.DeletedPencil) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    (out : h.residual≠⊥) :
    ∃ z∈h.residual, z≠0 ∧ h.residual=K∙z ∧ ∃ a t : K,
      ∀ i : Fin 20,z i≠0→nodes A i=a ∧ v i=t := by
  obtain ⟨z,hz,zn⟩ := h.residual.ne_bot_iff.mp out
  have r1 := (h.rank_split H).2
  have r : (K∙z)≤h.residual := (Submodule.span_singleton_le_iff_mem _ _).mpr hz
  have eq := Submodule.eq_of_le_of_finrank_le r (by rw [finrank_span_singleton zn]; exact r1)
  have run (c : Vec K 20) (inv : h.head.U.map (diag c)≤h.head.U) :
      ∃ a : K,∀ i : Fin 20,z i≠0→c i=a := by
    have t : diag c z∈h.residual := ghost_residual_diag inv (Submodule.mem_map_of_mem hz)
    rw [←eq] at t
    obtain ⟨a,e⟩ := Submodule.mem_span_singleton.mp t
    refine ⟨a,fun i zi => ?_⟩
    have m := congrFun e i
    change a*z i=c i*z i at m
    exact (mul_right_cancel₀ zi m).symm
  obtain ⟨a,haSite⟩ := run (nodes A) h.head.maximal.2.1
  obtain ⟨c,hc⟩ := run v (h.preserves_core D ha ho H)
  exact ⟨z,hz,zn,eq.symm,a,c,fun i e => ⟨haSite i e,hc i e⟩⟩

end Order15K2Head

namespace Order15K2Head
variable (h : Order15K2Head A b v) [CharZero K]

theorem ordinary_joint_values {x : Vec K 20} (pay : x∈treeSpace A 7) (a t : K) :
    ∃ α : K, ∃ y∈h.residual, ∀ i : Fin 20,
      i∉ghostPositions A b → nodes A i=a → v i=t → x i=α+y i := by
  obtain ⟨P,dp,pure⟩ := exists_poly_zeroSpace_charZero A pay
  rw [h.head.seven] at pure
  obtain ⟨u,hu,Q,_,eq⟩ := Clock.exists_head_poly pure
  rw [h.split.1] at hu
  obtain ⟨w,hw,y,hy,e⟩ := Submodule.mem_sup.mp hu
  refine ⟨P.eval a+Q.eval a*t,y,hy,fun i ng ia it=>?_⟩
  have r := eq i
  have r' := congrFun e i
  have w0 : w i=0 := ghostPositions_vanish (v:=w) hw ng
  simp only [h.physical,Pi.sub_apply,evalNodes_apply,ia,it] at r
  rw [Pi.add_apply,w0,zero_add] at r'
  rw [←r'] at r
  linear_combination r

set_option maxHeartbeats 1400000 in
theorem joint_restrict_cap (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) {n : ℕ} (idx : Fin n→Fin 20) (a t : K)
    (inj : Function.Injective idx) (nt : ∀ i,idx i≠Fin.last 19)
    (ng : ∀ i, idx i∉ghostPositions A b)
    (clock : ∀ i,nodes A (idx i)=a) (val : ∀ i,v (idx i)=t) :
    n≤1+finrank K (h.residual.map (restrictCol idx)) ∧
      ((1:Vec K n)∈h.residual.map (restrictCol idx) →
        n≤finrank K (h.residual.map (restrictCol idx))) := by
  let U := h.residual.map (restrictCol idx)
  let S := K∙(1:Vec K n)
  let E := (treeSpace A 7).map (restrictCol idx)
  have eTop : E=⊤ := order15_e7_fiber_restrict_top ha ho H idx inj nt a clock
  have rankE : finrank K E=n := by rw [eTop,finrank_top,Module.finrank_fin_fun]
  have eq : E≤S⊔U := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨α,y,hy,p⟩ := h.ordinary_joint_values hx a t
    refine Submodule.mem_sup.mpr ⟨α • (1:Vec K n),S.smul_mem _ (Submodule.subset_span rfl),
      restrictCol idx y,Submodule.mem_map_of_mem hy,?_⟩
    ext i
    simpa only [Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one,restrictCol_apply]
      using (p (idx i) (ng i) (clock i) (val i)).symm
  have k := Submodule.finrank_mono eq
  rw [rankE] at k
  have rk := Submodule.finrank_sup_add_finrank_inf_eq S U
  have rs : finrank K S≤1 := by
    by_cases z : (1:Vec K n)=0
    · change finrank K (K∙(1:Vec K n))≤1
      rw [z,Submodule.span_zero_singleton,finrank_bot]; decide
    · exact (finrank_span_singleton z).le
  change n≤1+finrank K U ∧ ((1:Vec K n)∈U → n≤finrank K U)
  refine ⟨by omega,fun x => ?_⟩
  have hSU : S≤U := (Submodule.span_singleton_le_iff_mem _ _).mpr x
  rwa [sup_eq_right.mpr hSU] at k

end Order15K2Head
end
end RKCert.Paired
