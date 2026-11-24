module

public import RKCert.ReviewedNative.ClockHeadFibers

public section

/-! # Chronological contrast on physical clock and multiplier values

Both masks act on the same original stages. The chronological proof
uses two successive block masks, not synthetic relabeling of stages or
values; it works over an arbitrary field. -/
namespace RKResearch.Certified.Graded.HeadFiber

open RKCert.OneEscape RKCert.Endpoint Polynomial
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ} {c v w z : Fin s → K}
variable {U : Submodule K (Fin s → K)}

/-- The first failed global chronological match fails in its own
joint clock-and-multiplier block. -/
theorem first_unmatched_joint_block (hc : MaskInvariant c U) (hv : MaskInvariant v U)
    (outside : z∉U) :
    ∃ k : Fin s, ∃ g∈U, (∀ i < k, g i=z i) ∧
      ¬∃ t∈U, ∀ i : Fin s, i.val<k.val+1 → c i=c k → v i=v k → t i=z i := by
  classical
  let M (n : ℕ) := ∃ a∈U, ∀ i : Fin s, i.val<n → a i=z i
  have hex : ∃ n, ¬M n := by
    refine ⟨s,fun ⟨a,ha,all⟩ => outside ?_⟩
    have eq : a=z := funext (fun i => all i i.isLt)
    exact eq ▸ ha
  let n := Nat.find hex
  have fail : ¬M n := Nat.find_spec hex
  have ns : n≤s := by
    apply Nat.find_min' hex
    rintro ⟨a,ha,all⟩
    exact outside ((funext (fun i : Fin s => all i i.isLt) : a=z) ▸ ha)
  have positive : 0<n := by
    by_contra! zero
    have eq : n=0 := by omega
    apply fail
    exact ⟨0,U.zero_mem,fun i hi => False.elim (by omega)⟩
  let k : Fin s := ⟨n-1,by omega⟩
  have kn : k.val+1=n := by dsimp [k]; omega
  obtain ⟨g,gu,pre⟩ := (not_not.mp (Nat.find_min hex (by omega : k.val<n)) : M k.val)
  refine ⟨k,g,gu,pre,fun ⟨t,tu,last⟩ => fail ?_⟩
  let y := g+blockMask v (v k) (blockMask c (c k) (t-g))
  refine ⟨y,U.add_mem gu (hv _ _ (hc _ _ (U.sub_mem tu gu))),?_⟩
  intro i hi
  by_cases ci : c i=c k
  · by_cases vi : v i=v k
    · simp [y,blockMask,ci,vi,last i (by omega) ci vi]
    · have before : i.val<k.val := by
        by_contra! h
        exact vi (congrArg v (Fin.ext (by omega) : i=k))
      simp [y,blockMask,vi,pre i before]
  · have before : i.val<k.val := by
      by_contra! h
      exact ci (congrArg c (Fin.ext (by omega) : i=k))
    simp [y,blockMask,ci,pre i before]

/-- At a joint first failure of a tested polynomial multiplier, every
paid head column which is constant on that joint prefix has value zero
there. Subsequent paid chronology can use the same detected row. -/
theorem joint_prefix_detector (hc : MaskInvariant c U) (hv : MaskInvariant v U)
    (P Q : K[X]) (profile : v*w-weightedEval c w P∈U)
    (val : ∀ i, z i=Q.eval (c i)*(P.eval (c i)-v i)) (outside : z∉U) :
    ∃ k : Fin s, ∃ g∈U, (∀ i<k, g i=z i) ∧ Q.eval (c k)≠0 ∧
      ∀ {n : ℕ} {f : Fin s → K}, f∈chain (diag c) U w n → ∀ a : K,
        (∀ i : Fin s, i.val<k.val+1 → c i=c k → v i=v k → f i=a) → a=0 := by
  classical
  obtain ⟨k,g,gu,pre,bad⟩ := first_unmatched_joint_block hc hv outside
  have zlocal (i : Fin s) (ci : c i=c k) (vi : v i=v k) : z i=z k := by
    rw [val i,ci,vi,←val k]
  have zn : z k≠0 := by
    intro eq
    exact bad ⟨0,U.zero_mem,fun i _ ci vi => by rw [zlocal i ci vi,eq,Pi.zero_apply]⟩
  have nz : Q.eval (c k)≠0 ∧ P.eval (c k)-v k≠0 :=
    mul_ne_zero_iff.mp (val k ▸ zn)
  let M (x : Fin s → K) := blockMask v (v k) (blockMask c (c k) x)
  have m (x : Fin s → K) (h : x∈U) : M x∈U := hv _ _ (hc _ _ h)
  have prof : M (v*w-weightedEval c w P)=(v k-P.eval (c k)) • M w := by
    ext i
    by_cases ci : c i=c k <;> by_cases vi : v i=v k <;>
      simp [M,blockMask,ci,vi,sub_mul]
  have head : M w∈U := by
    have h := m _ profile
    rw [prof] at h
    exact (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr
      (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp nz.2))))).mp h
  refine ⟨k,g,gu,pre,nz.1,fun {n f} h a constant => ?_⟩
  obtain ⟨u,hu,L,_,repr⟩ := exists_poly h
  have eq : M f=M u+L.eval (c k) • M w := by
    ext i
    by_cases ci : c i=c k <;> by_cases vi : v i=v k <;> simp [M,blockMask,ci,vi,repr]
  have inU : M f∈U := eq.symm ▸ U.add_mem (m _ hu) (U.smul_mem _ head)
  by_contra nonzero
  apply bad
  refine ⟨(z k/a) • M f,U.smul_mem _ inU,fun i hi ci vi => ?_⟩
  rw [zlocal i ci vi]
  simp only [M,blockMask,ci,vi,ite_true,Pi.smul_apply,smul_eq_mul,constant i hi ci vi]
  exact div_mul_cancel₀ _ nonzero

end RKResearch.Certified.Graded.HeadFiber
