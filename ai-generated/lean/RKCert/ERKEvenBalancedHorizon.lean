module
public import RKCert.ERKEvenBalancedRanks
public import RKCert.ERKPrimitiveReverseGain
public import RKCert.ERKUnitReverseLocalChart
public import RKCert.NodalOrbitBudget

@[expose] public section
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint RKCert.Paired.Clock Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

omit [CharZero K] in
theorem annihilating_terminal_count {U V:Submodule K (Vec K s)} (z:Vec K s) (out:z∉U)
    (inc:V≤annih U) (zero:∀w∈V,row w z=0) : finrank K U+finrank K V+1≤s := by
  let W:=U⊔Submodule.span K {z}
  have lt:U<W := lt_of_le_of_ne le_sup_left (fun he=>out (he ▸
    (show z∈W from (show Submodule.span K {z}≤W from le_sup_right) (Submodule.mem_span_singleton_self z))))
  have a:=Submodule.finrank_lt_finrank_of_lt lt
  have b:=finrank_annih_le (V:=V) (U:=W) (by
    intro w hw
    apply mem_annih.mpr
    change W≤(row w).ker
    exact sup_le (mem_annih.mp (inc hw)) ((Submodule.span_singleton_le_iff_mem ..).mpr (zero w hw)))
  omega

theorem residual_eq_reflectedError (k:ℕ) :
    RKCert.Paired.OrderTwelve.reverseResidual A b k=reflectedError A b (X^k) := by
  have we (l:ℕ):reflWeight A b l=weightedEval (mirror A) b (X^l) := by
    ext i;simp [reflWeight,reflNode,mirror,weightedEval_apply]
  have fp : formalPrimitive (X^k:K[X]) = C (((k+1:ℕ):K)⁻¹)*X^(k+1) := by
    rw [formalPrimitive_eq_treePrimitive]
    calc
      _ = primitive (monomial k (1:K)) := by simp [←C_mul_X_pow_eq_monomial]
      _ = _ := by rw [primitive_monomial,←C_mul_X_pow_eq_monomial,one_div]
  rw [RKCert.Paired.OrderTwelve.reverseResidual_eq _ _ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)),
    reflectedError_apply,we,we,fp,Polynomial.C_mul',map_smul]
 
theorem orbitBand_le_primitiveBack (n:ℕ) :
    orbitBand (mirror A) (backSeed2 A b) n≤primitiveBack A b n := by
  classical
  have mono:Monotone (primitiveBack A b) := monotone_nat_of_le_succ primitiveBack_le_succ
  have pw (k:ℕ) : (diag (mirror A)^k) (backSeed2 A b)∈primitiveBack A b (k+1) := by
    induction k with
    | zero => simpa only [pow_zero,one_apply_eq_self] using
        (seed2_mem_primitiveBack (A:=A) (b:=b) 0)
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp]
      exact primitiveBack_clock (k+1) (Submodule.mem_map_of_mem ih)
  rintro _ ⟨a,rfl⟩
  let f:=ofFn n a
  let E:=weightedEval (mirror A) (backSeed2 A b)
  change E f∈primitiveBack A b n
  by_cases n0:n=0
  · subst n
    simp [f]
  rw [f.as_sum_range' n (ofFn_natDegree_lt (Nat.pos_of_ne_zero n0) a),map_sum]
  apply (primitiveBack A b n).sum_mem
  intro k hk
  have eq:E (monomial k (f.coeff k))=f.coeff k • (diag (mirror A)^k) (backSeed2 A b) := by
    ext i;simp [E,eval_monomial,pow_diag_apply,smul_eq_mul,mul_assoc]
  rw [eq]
  exact (primitiveBack A b n).smul_mem _ (mono (by have :=Finset.mem_range.mp hk;omega) (pw k))

end RKCert.Paired.ReverseHull

namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.Paired.OrderTwelve RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

structure EvenThinHorizon (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q:ℕ) : Prop where
  exactRanks : ∀n≤q-1,finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n
  gaps : ∀n,2≤n→n≤q-1→¬(primitiveBack A b n).map (diag (mirror A))≤primitiveBack A b n
  manySites : q≤(orbitSites (mirror A) (backSeed2 A b)).card
  band : (annih (treeSpace A (q-1))⊓LinearMap.ker (LinearMap.proj (Fin.last s))) =
    orbitBand (mirror A) (backSeed2 A b) (q-1)

set_option maxHeartbeats 2000000 in
/-- A balanced actual even tableau has the entire thin reverse horizon.
No primitive membership, moment-location restriction, or head cardinal is
assumed, including at a potentially localized one-node reverse seed. -/
theorem balanced_even_thin_horizon (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (q9:9≤q) (size:s+1=3*q) (S:EvenBalanced A b q) : EvenThinHorizon A b q := by
  classical
  let t:=Fin.last s
  let H:=q-1
  let d:=backSeed2 A b
  let y:=mirror A
  let L:=primitiveBack A b
  have cl:∀i,A i t=0 := fun i=>ha i t (Fin.le_last i)
  have last (n:ℕ) {w:Vec K (s+1)} (hw:w∈L n) : row w (terminal s)=0 := by
    rw [row_terminal]
    exact primitiveBack_terminal t S.lastReflect cl S.seedZero n hw
  have capH : finrank K (L H)≤H := by
    have D:=annihilating_terminal_count (terminal s) S.terminalOut
      (primitiveBack_annih ho (q-1) H (by dsimp [H];omega)) (fun _ hw=>last H hw)
    change finrank K (treeSpace A (q-1))+finrank K (L H)+1≤s+1 at D
    rw [S.treePrev] at D
    have hH:H=q-1:=rfl
    omega
  have thin:=thin_primitiveBack_agrees ha ho (by dsimp [H];omega) capH
  have ranks (n:ℕ) (hn:n≤H) : finrank K (L n)=n := by
    change finrank K (primitiveBack A b n)=n
    rw [←(thin n hn).2,(thin n hn).1]
  have ep:2*q-3≤finrank K (treeSpace A (q-2)) := by
    have five:=grade_five_surplus ha (S.separated.mono (by omega : 5≤q))
    have G:=strict_rank_interval ha S.separated 5 (q-7) (by omega) (by omega)
    rw [show 5+(q-7)=q-2 by omega] at G
    have A:=tree_rank_eq ho (S.separated.mono (by omega : q-2≤q)) (by omega)
    omega
  have outP:terminal (K:=K) s∉treeSpace A (q-2) := fun h=>S.terminalOut (treeSpace_mono A (by omega) h)
  have capMore:finrank K (L (H+1))≤q+2 := by
    have D:=annihilating_terminal_count (terminal s) outP
      (primitiveBack_annih ho (q-2) (H+1) (by dsimp [H];omega)) (fun _ hw=>last (H+1) hw)
    change finrank K (treeSpace A (q-2))+finrank K (L (H+1))+1≤s+1 at D
    omega
  have escapes (n:ℕ) (low:2≤n) (hi:n≤H) : ¬(L n).map (diag y)≤L n := by
    intro inv
    have G:=primitiveBack_invariant_gain ha ho n (by dsimp [H] at hi;omega) inv
    change finrank K (L n)+(n+2)/2≤finrank K (L (n+1)) at G
    rw [ranks n hi] at G
    by_cases eq:n=H
    · rw [eq] at G
      dsimp [H] at *
      omega
    · rw [ranks (n+1) (by omega)] at G
      omega
  have early : UnitFirstFour A b := by
    refine ⟨S.seedZero,fun n hn=>(thin n (by dsimp [H];omega)).1,?_,?_,?_,?_⟩
    · rw [(thin 2 (by dsimp [H];omega)).2]
      exact escapes 2 (by decide) (by dsimp [H];omega)
    · rw [(thin 3 (by dsimp [H];omega)).2]
      exact escapes 3 (by decide) (by dsimp [H];omega)
    · rw [(thin 2 (by dsimp [H];omega)).2,residual_eq_reflectedError]
      exact reflectedError_mem_primitiveBack (X^2) 1 (by simp)
    · rw [(thin 3 (by dsimp [H];omega)).2,residual_eq_reflectedError]
      exact reflectedError_mem_primitiveBack (X^3) 2 (by simp)
  have nonEmpty:(orbitSites y d).card≠0 := by
    intro e
    have dz:d=0 := by
      ext i
      by_contra dn
      exact (Finset.card_ne_zero.mpr ⟨_,Clock.headSites_mem (c:=y) i dn⟩) e
    have B0:back A b 0=⊥ := Submodule.finrank_eq_zero.mp (early.rank 0 (by decide))
    have B1:back A b 1=⊥ := by
      change back A b 0⊔(back A b 0).map (transMat A)⊔(back A b 0).map (diag y)⊔(K∙d)=⊥
      simp [B0,dz]
    have R:finrank K (back A b 1)=1:=early.rank 1 (by decide)
    have Z:=Submodule.finrank_eq_zero.mpr B1
    omega
  have enough:q≤(orbitSites y d).card := by
    by_contra! small
    let n:ℕ:=(orbitSites y d).card
    have hi:n≤H := by dsimp only [n,H];omega
    have no1:n≠1 := unit_no_single_reverse_site ha ho (by omega) early
    have lo:2≤n := by have z:n≠0:=nonEmpty;omega
    have all : orbitBand y d n=nodalOrbit y d := by
      apply Submodule.eq_of_le_of_finrank_le (orbitBand_le y d n)
      rw [orbitBand_rank y d n le_rfl,nodalOrbit_rank]
    have eq : nodalOrbit y d=L n := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [←all]
        exact orbitBand_le_primitiveBack (A:=A) (b:=b) n
      · rw [nodalOrbit_rank,ranks n hi]
    apply escapes n lo hi
    rw [←eq]
    rintro _ ⟨w,hw,rfl⟩
    have res:=mulByBlock_mem y (nodalOrbit_mask y d) (fun a=>a) hw
    exact res
  have band:orbitBand y d H=L H := by
    apply Submodule.eq_of_le_of_finrank_le (orbitBand_le_primitiveBack (A:=A) (b:=b) H)
    rw [ranks H le_rfl,orbitBand_rank y d H (by dsimp [H];omega)]
  exact ⟨thin,escapes,enough,S.reversePrev.symm.trans ((thin H le_rfl).2.trans band.symm)⟩

end RKCert.Paired.FiniteMidpoint
