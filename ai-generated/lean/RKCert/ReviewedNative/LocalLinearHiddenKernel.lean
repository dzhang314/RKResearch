module

public import RKCert.ReviewedNative.LocalLinearInvisible

@[expose] public section

/-! # The genuine product-closed invisible kernel of the local linear band -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
variable {r : ℕ} {U : Submodule K (Fin s→K)} {τ : Fin s→K}

def hiddenKernel (b τ : Fin s→K) (U : Submodule K (Fin s→K)) :
    Submodule K (Fin s→K) :=
  (LinearMap.ker (diag τ) ⊓ U.comap (diag b)) ⊓ ⨅ w : U, U.comap (diag w.val)

private theorem diag_eq_mul (a v : Fin s→K) : diag a v=a*v := by ext i; simp

theorem mem_hiddenKernel {v : Fin s→K} : v∈hiddenKernel b τ U ↔
    τ*v=0 ∧ b*v∈U ∧ U.map (diag v)≤U := by
  simp only [hiddenKernel,Submodule.mem_inf,LinearMap.mem_ker,Submodule.mem_comap,
    Submodule.mem_iInf,diag_eq_mul]
  constructor
  · rintro ⟨⟨t,w⟩,i⟩
    refine ⟨t,w,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    rw [diag_eq_mul,mul_comm]
    exact i ⟨z,hz⟩
  · rintro ⟨t,w,i⟩
    exact ⟨⟨t,w⟩,fun z=>by
      rw [mul_comm,←diag_eq_mul]
      exact i (Submodule.mem_map_of_mem z.prop)⟩

theorem hiddenKernel_mul {x y : Fin s→K}
    (hx : x∈hiddenKernel b τ U) (hy : y∈hiddenKernel b τ U) : x*y∈hiddenKernel b τ U := by
  have ⟨tx,bx,ux⟩ := mem_hiddenKernel.mp hx
  have ⟨ty,by',uy⟩ := mem_hiddenKernel.mp hy
  apply mem_hiddenKernel.mpr
  refine ⟨by rw [←mul_assoc,tx,zero_mul],?_,?_⟩
  · have dz : diag x (b*y)=b*(x*y) := by rw [diag_eq_mul]; ac_rfl
    rw [←dz]
    exact ux (Submodule.mem_map_of_mem by')
  · rintro _ ⟨w,hw,rfl⟩
    have ez : diag (x*y) w=diag x (diag y w) := by simp only [diag_eq_mul,mul_assoc]
    rw [ez]
    exact ux (Submodule.mem_map_of_mem (uy (Submodule.mem_map_of_mem hw)))

theorem hiddenKernel_clock {c : Fin s→K} (stable : U.map (diag c)≤U) :
    (hiddenKernel b τ U).map (diag c)≤hiddenKernel b τ U := by
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨t,w,u⟩ := mem_hiddenKernel.mp hv
  apply mem_hiddenKernel.mpr
  refine ⟨?_,?_,?_⟩
  · rw [diag_eq_mul,show τ*(c*v)=c*(τ*v) by ac_rfl,t,mul_zero]
  · rw [diag_eq_mul,show b*(c*v)=c*(b*v) by ac_rfl,←diag_eq_mul]
    exact stable (Submodule.mem_map_of_mem w)
  · rintro _ ⟨z,hz,rfl⟩
    rw [show diag (diag c v) z=diag c (diag v z) by simp only [diag_eq_mul,mul_assoc]]
    exact stable (Submodule.mem_map_of_mem (u (Submodule.mem_map_of_mem hz)))

theorem hiddenKernel_forward_clock (F : LocalLinearBand A b 8 r U τ) :
    (hiddenKernel b τ U).map (diag (nodes A))≤hiddenKernel b τ U := by
  apply hiddenKernel_clock
  rintro _ ⟨u,hu,rfl⟩
  have e : diag (nodes A) u=u-diag (reflectedClock A) u := by
    ext i
    simp only [diag_apply,Pi.sub_apply,reflectedClock,Pi.one_apply]
    ring
  rw [e]
  exact U.sub_mem hu (F.invariant (Submodule.mem_map_of_mem hu))

theorem hiddenKernel_le_midpoint_tree (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) :
    hiddenKernel b τ U≤treeSpace A 9 := by
  intro v hv
  obtain ⟨ht,hb,hu⟩ := mem_hiddenKernel.mp hv
  rw [←annih_annih (treeSpace A 9),←full]
  apply mem_annih.mpr
  intro w hw
  have rb : r≤8 := by rcases F.coreRank with e|e <;> omega
  rw [F.band 8 rb le_rfl] at hw
  obtain ⟨u,hU,Q,_,eq⟩ := HeadFiber.exists_poly hw
  have vone (z : Fin s→K) (hz : z∈U) : row v z=0 := by
    have prod := hu (Submodule.mem_map_of_mem hz : diag v z∈U.map (diag v))
    have ones : (1 : Fin s→K)∈treeSpace A 9 := by
      have e : evalNodes A (1 : K[X])=(1 : Fin s→K) := by ext i; simp
      rw [←e]
      exact evalNodes_mem_treeSpace A _ (by simp)
    have coreIn : U≤primitiveBack A b 8 := F.core.le.trans
      ((monotone_nat_of_le_succ (adjointFlag_le_succ _)) (by omega))
    have orth : row (diag v z) 1=0 := mem_annih.mp (full.le (coreIn prod)) 1 ones
    simpa only [row_apply,dotProduct,Pi.one_apply,diag_apply,mul_one] using orth
  have two : row v (weightedEval (reflectedClock A) τ Q)=0 := by
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    have e : τ i*v i=0 := congrFun ht i
    simp only [weightedEval_apply]
    rw [show v i*(Q.eval (reflectedClock A i)*τ i)=Q.eval (reflectedClock A i)*(τ i*v i) by ring,
      e,mul_zero]
  rw [eq,map_add,vone u hU,two,add_zero]

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem grade_four_le_hiddenKernel (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) (pay : 19≤p) :
    zeroSpace A 4≤hiddenKernel b τ U :=
  fun _ hf=>mem_hiddenKernel.mpr (local_linear_invisible_four ha ho F full pay hf)

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
