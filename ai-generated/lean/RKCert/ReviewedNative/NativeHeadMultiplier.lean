module

public import RKCert.ReviewedNative.ClockHeadFibers
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

/-! # Multipliers on a native one-head chart

An active clock is counted only if its head block escapes the invariant
core. Polynomial uniqueness on these actual blocks bounds the degree
of any true multiplier profile, without choosing a normalized head. -/
namespace RKResearch.Certified.Graded.HeadFiber
open RKCert.OneEscape RKCert.Endpoint Polynomial
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ} {c v w : Fin s → K}
variable {U : Submodule K (Fin s → K)} {n r : ℕ}

theorem faithful_on_escape_sites (hU : U.map (diag c) ≤ U)
    {P : K[X]} (dP : P.degree < ((escapeSites c w U).card:WithBot ℕ))
    (hp : weightedEval c w P∈U) : P=0 := by
  classical
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (escapeSites c w U) dP
  intro a ha
  have mask := clock_mask_invariant (fun u (hu : u∈U) => hU (Submodule.mem_map_of_mem hu))
  have e : blockMask c a (weightedEval c w P) = P.eval a • blockMask c a w := by
    ext i
    by_cases e : c i=a <;> simp [blockMask,e]
  have hm := mask a _ hp
  rw [e] at hm
  by_contra nz
  exact (Finset.mem_filter.mp ha).2 ((U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nz)).mp hm)

theorem multiplier_profile_of_chart
    (hU : U.map (diag c) ≤ U) (hV : U.map (diag v) ≤ U)
    (many : n < (escapeSites c w U).card) (rp : 0<r)
    (band : ∀ k < r, v*((diag c^k) w) ∈ chain (diag c) U w n)
    (vin : v∈chain (diag c) U w r) (out : v∉U) :
    ∃ P : K[X], P≠0 ∧ P.natDegree+r≤n ∧ v*w-weightedEval c w P∈U := by
  classical
  have fit (k : ℕ) (hk : k<r) :
      ∃ P : K[X], P.degree < (n:WithBot ℕ) ∧ v*((diag c^k) w)-weightedEval c w P∈U := by
    obtain ⟨u,hu,P,d,e⟩ := exists_poly (band k hk)
    refine ⟨P,d,?_⟩
    rw [e,add_sub_cancel_right]
    exact hu
  obtain ⟨P,d,profile⟩ := fit 0 rp
  have base : v*w-weightedEval c w P∈U := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using profile
  have vstable (u : Fin s → K) (hu : u∈U) : diag v u ∈ U := hV (Submodule.mem_map_of_mem hu)
  have cstable (u : Fin s → K) (hu : u∈U) : diag c u ∈ U := hU (Submodule.mem_map_of_mem hu)
  have nz : P≠0 := by
    intro pz
    have vw : v*w∈U := by simpa only [pz,map_zero,sub_zero] using base
    obtain ⟨u,hu,Q,_,e⟩ := exists_poly vin
    have h := U.add_mem (vstable u hu) (clock_function_mem cstable (fun x => Q.eval x) vw)
    have eq : diag v u+(fun i=>Q.eval (c i)*(v*w) i) = v*v := by
      ext i
      simp only [Pi.add_apply,diag_apply,Pi.mul_apply]
      have h := congrFun e i
      simp only [Pi.add_apply,weightedEval_apply] at h
      calc
        _ = v i*(u i + Q.eval (c i)*w i) := by ring
        _ = _ := by rw [←h]
    rw [eq] at h
    have mem := clock_function_mem vstable (fun x=>x⁻¹) h
    have cancel : (fun i=> (v i)⁻¹*(v*v) i) = v := by
      ext i
      simp only [Pi.mul_apply,←mul_assoc]
      by_cases z : v i=0 <;> simp [z]
    exact out (cancel ▸ mem)
  have power (k : ℕ) : v*((diag c^k) w)-weightedEval c w (X^k*P)∈U := by
    convert clock_function_mem cstable (fun x=>x^k) base using 1
    ext i
    simp only [Pi.sub_apply,Pi.mul_apply,clock_power_value,weightedEval_apply,eval_mul,eval_pow,eval_X]
    ring
  have grow (k : ℕ) (hk : k<r) : (X^k*P).degree < (n:WithBot ℕ) := by
    induction k with
    | zero => simpa using d
    | succ k ih =>
      obtain ⟨Q,dQ,pQ⟩ := fit (k+1) hk
      have dif : weightedEval c w (X^(k+1)*P-Q)∈U := by
        rw [map_sub]
        convert U.sub_mem pQ (power (k+1)) using 1
        abel
      have dX : (X^(k+1)*P).degree < ((escapeSites c w U).card:WithBot ℕ) := by
        have hn := mul_ne_zero (pow_ne_zero k X_ne_zero) nz
        have dg := (natDegree_lt_iff_degree_lt hn).mpr (ih (by omega))
        rw [pow_succ',mul_assoc]
        apply (natDegree_lt_iff_degree_lt (mul_ne_zero X_ne_zero hn)).mp
        rw [natDegree_X_mul hn]
        omega
      have de := (degree_sub_le (X^(k+1)*P) Q).trans_lt
        (max_lt dX (dQ.trans (by exact_mod_cast many)))
      have e := sub_eq_zero.mp (faithful_on_escape_sites hU de dif)
      rwa [e]
  have dlast := grow (r-1) (by omega)
  have last := (natDegree_lt_iff_degree_lt (mul_ne_zero (pow_ne_zero (r-1) X_ne_zero) nz)).mpr dlast
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) nz,natDegree_X_pow] at last
  exact ⟨P,nz,by omega,base⟩

end RKResearch.Certified.Graded.HeadFiber
