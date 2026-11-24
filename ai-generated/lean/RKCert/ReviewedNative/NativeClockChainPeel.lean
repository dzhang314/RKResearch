module

public import RKCert.ReviewedNative.NativeClockStaircase

@[expose] public section

/-! # Removing an unpaid leading clock power -/
namespace RKResearch.Certified.Graded

open Module RKCert.OneEscape
open scoped Classical
variable {K : Type*} [Field K]

section Head
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {D : V →ₗ[K] V} {U : Submodule K V} {w x : V}

/-- If the next clock power is unpaid, a vector that stays in the chain
under one clock shift already lies in the chain with its last term removed. -/
theorem clock_chain_drop_of_next_unpaid (stable : U.map D≤U) (n : ℕ)
    (unpaid : (D^(n+1)) w∉chain D U w (n+1))
    (hx : x∈chain D U w (n+1)) (hd : D x∈chain D U w (n+1)) :
    x∈chain D U w n := by
  let B := chain D U w (n+1)
  change x∈chain D U w n⊔(K ∙ ((D^n) w)) at hx
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hz
  have move : (chain D U w n).map D≤B := by
    cases n with
    | zero =>
      exact stable.trans ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) 1).mp le_rfl).1
    | succ k =>
      exact le_sup_right.trans (clock_chain_next stable (Nat.succ_pos k)).le
  have huD : D u∈B := move (Submodule.mem_map_of_mem hu)
  have e : D ((D^n) w)=(D^(n+1)) w := by
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
  rw [map_add,map_smul,e] at hd
  have ht : t • (D^(n+1)) w∈B := by
    simpa only [add_sub_cancel_left] using B.sub_mem hd huD
  have tz : t=0 := by
    by_contra tn
    exact unpaid ((B.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr tn)).mp ht)
  simpa only [tz,zero_smul,add_zero] using hu
end Head

end RKResearch.Certified.Graded
