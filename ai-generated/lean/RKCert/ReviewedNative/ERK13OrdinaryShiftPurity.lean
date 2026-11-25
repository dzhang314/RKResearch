module

public import RKCert.ReviewedNative.ERK13NativeOrdinaryStaircase
public import RKCert.ReviewedNative.NativeHeadMultiplier
public import RKCert.ReviewedNative.NativePrimitiveMoments
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Adjacent grade-eight shifts remove polynomial leakage

No radius-two assumption is needed. In particular the two paid
grade-four head columns in radius three give pure square payment.
The grade-three multiplication conclusion retains provenance and is
independent of the later matched-block primitive port.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w x : Fin 19→K} {r : ℕ} {G : K[X]}

private abbrev B (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19→K)) (w : Fin 19→K) (n : ℕ) :=
  chain (diag (nodes A)) U w n

private theorem rank_band (n : ℕ) :
    finrank K (B A U w n)≤finrank K U+n := by
  induction n with
  | zero =>
    change finrank K U ≤ finrank K U + 0
    exact Nat.le_refl _
  | succ n ih =>
    by_cases paid : (diag (nodes A)^n) w∈B A U w n
    · have eq : B A U w (n+1)=B A U w n :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr paid)
      rw [eq]
      omega
    · change finrank K (↥(B A U w n ⊔ (K ∙ ((diag (nodes A)^n) w)) : Submodule K (Fin 19 → K))) ≤ _
      rw [Submodule.finrank_sup_span_singleton paid]
      omega

private theorem chart_discards_polynomial (ho : HasOrder 13 A b) {j n : ℕ}
    (chart : treeSpace A j=(coeffEval A 6).range⊔B A U w n)
    (rank : finrank K (treeSpace A j)=7+finrank K U+n)
    {P : K[X]} (d : P.natDegree≤6) (mem : evalNodes A P∈B A U w n) : P=0 := by
  let V := (coeffEval A 6).range
  have rc : finrank K V≤7 := (LinearMap.finrank_range_le (coeffEval A 6)).trans_eq
    (Module.finrank_fin_fun K)
  have rb := rank_band (A:=A) (U:=U) (w:=w) n
  have dim := Submodule.finrank_sup_add_finrank_inf_eq V (B A U w n)
  rw [show V⊔B A U w n=treeSpace A j from chart.symm,rank] at dim
  have dis : V⊓B A U w n=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have cp : evalNodes A P∈V := ⟨_,(evalNodes_eq_coeffEval A P d).symm⟩
  have both : evalNodes A P∈V⊓B A U w n := ⟨cp,mem⟩
  rw [dis,Submodule.mem_bot] at both
  apply (PolySeparated.of_coeff (coeff_separated ho (q:=6) (by decide))) P d
  rw [both]
  exact (zeroSpace A 6).zero_mem

private theorem chart_expand {j n : ℕ}
    (chart : treeSpace A j=(coeffEval A 6).range⊔B A U w n)
    (mem : x∈treeSpace A j) :
    ∃ (P : K[X]) (h : Fin 19→K), P.natDegree≤6 ∧ h∈B A U w n ∧
      x=evalNodes A P+h := by
  rw [chart] at mem
  obtain ⟨_,⟨a,rfl⟩,h,hh,he⟩ := Submodule.mem_sup.mp mem
  let P := ofFn 7 a
  have d : P.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
  have ev : evalNodes A P=coeffEval A 6 a := by
    rw [evalNodes_eq_coeffEval A P d]
    congr 1
    ext i
    exact ofFn_coeff_eq_val_of_lt _ i.isLt
  exact ⟨P,h,d,hh,by rw [ev,he]⟩

private theorem at_origin (ha : ∀ i j,i≤j → A i j=0) {P : K[X]} {j : ℕ}
    (mem : evalNodes A P∈zeroSpace A j) : P.eval 0=0 := by
  have z := origin_zeroSpace ha j mem
  change P.eval (nodes A (0 : Fin 19))=0 at z
  have c0 : nodes A (0 : Fin 19)=0 := by
    change (∑ i,A 0 i*1)=0
    exact Finset.sum_eq_zero (fun i _=>by rw [ha 0 i (Fin.zero_le _),zero_mul])
  simpa only [c0] using z

private theorem paid_moment (ho : HasOrder 13 A b) {j k : ℕ} {P : K[X]}
    (dp : k+P.natDegree+1≤13) (pay : j+k+1≤13)
    (mem : evalNodes A P∈zeroSpace A j) :
    (primitive (X^k*P)).eval 1=0 :=
  (probe_evalNodes ho P k dp).symm.trans (probe_zeroSpace (k:=k) ho (by omega) mem)

private def mu (K : Type*) [Field K] (k : ℕ) : K[X] →ₗ[K] K :=
  (Polynomial.leval 1).comp (primitive.comp (LinearMap.mulLeft K (X^k:K[X])))

private theorem moment_band_detect {P : K[X]} {n : ℕ}
    (d : P.natDegree≤n+1) (o : P.eval 0=0)
    (z : ∀ k : Fin (n+1), mu K k.val P=0) : P=0 := by
  obtain ⟨Q,hQ⟩ : (X : K[X]) ∣ P := by
    simpa using (dvd_iff_isRoot (a:=(0:K))).mpr o
  by_cases eq : Q=0
  · simp [hQ,eq]
  · have qd : Q.natDegree≤n := by
      rw [hQ,natDegree_X_mul eq] at d
      omega
    have qz := NativeMoments.x_moments_detect qd (fun k=>by
      have t := z k
      rw [hQ] at t
      exact t)
    exact (eq qz).elim

private theorem deg_trim {P Q : K[X]} {a : K}
    (pd : P.natDegree≤7) (qd : Q.natDegree≤7)
    (top : P.coeff 7=a*Q.coeff 7) : (P-a • Q).natDegree≤6 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  by_cases e : k=7
  · subst k
    simp only [coeff_sub,Polynomial.coeff_smul,smul_eq_mul,top,sub_self]
  · rw [coeff_sub,Polynomial.coeff_smul,coeff_eq_zero_of_natDegree_lt (pd.trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt (qd.trans_lt (by omega)),smul_zero,sub_zero]

private theorem band_succ (n : ℕ) : B A U w n≤B A U w (n+1) := le_sup_left

private theorem band_move (stable : U.map (diag (nodes A))≤U) {n : ℕ} (pos : 0<n)
    {v : Fin 19→K} (hv : v∈B A U w n) : diag (nodes A) v∈B A U w (n+1) := by
  have eq := clock_chain_next (w:=w) stable pos
  change diag (nodes A) v ∈ chain (diag (nodes A)) U w (n+1)
  rw [←eq]
  exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hv)

private theorem chart_growth_sites (stable : U.map (diag (nodes A))≤U) {j n : ℕ}
    (pos : 0<n) (e₀ : treeSpace A j=(coeffEval A 6).range⊔B A U w n)
    (e₁ : treeSpace A (j+1)=(coeffEval A 6).range⊔B A U w (n+1))
    (strict : finrank K (treeSpace A j)<finrank K (treeSpace A (j+1))) :
    n<(HeadFiber.escapeSites (nodes A) w U).card := by
  apply HeadFiber.more_escape_sites stable pos
  intro inv
  have eq : B A U w (n+1)=B A U w n :=
    (clock_chain_next stable pos).symm.trans (sup_eq_left.mpr inv)
  exact (ne_of_lt strict) (congrArg (fun S : Submodule K (Fin 19→K)=>finrank K S) (e₀.trans (by rw [e₁,eq])))

/-- Primitive moments exclude a nonzero polynomial projection from two
successive clock multiples when both are genuine F8 defects. -/
theorem ordinary_adjacent_shift_pure (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G r U w)
    (hx : x∈zeroSpace A 8) (hcx : diag (nodes A) x∈zeroSpace A 8) :
    x∈chain (diag (nodes A)) U w (r+3) := by
  have stable := H.paidHead.head.coreStable
  have bounds := H.paidHead.headBounds
  have rU := H.paidHead.head.baseRank
  rw [H.paidHead.five] at rU
  have Gp : evalNodes A G∈B A U w (r+2) := by
    have z := H.first.paid
    simpa only [H.paidHead.escapeShape,terminalMark,if_neg seed,sup_bot_eq] using z
  have Gd : G.natDegree=7 := H.first.degree
  have Gzero (k : ℕ) (hk : k≤5) : mu K k G=0 :=
    paid_moment ho (j:=7) (P:=G) (by omega) (by omega) (H.headSeven.symm ▸ Gp)
  have B8 : B A U w (r+3)≤zeroSpace A 8 := by
    change chain (diag (nodes A)) U w (r+3) ≤ zeroSpace A 8
    rw [←show r+2+1=r+3 by omega,←clock_chain_next stable (by omega : 0<r+2),←H.headSeven]
    exact sup_le (zeroSpace_mono A (by decide))
      (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 7))
  obtain ⟨P,h,d,hh,hEq⟩ := chart_expand H.treeEight (zeroSpace_le_treeSpace A 8 hx)
  obtain ⟨Q,t,e,ht,tEq⟩ := chart_expand H.treeEight (zeroSpace_le_treeSpace A 8 hcx)
  have memP : evalNodes A P∈zeroSpace A 8 := by
    have z := (zeroSpace A 8).sub_mem hx (B8 hh)
    rwa [hEq,add_sub_cancel_right] at z
  have memQ : evalNodes A Q∈zeroSpace A 8 := by
    have z := (zeroSpace A 8).sub_mem hcx (B8 ht)
    rwa [tEq,add_sub_cancel_right] at z
  have P0 := at_origin ha memP
  have Q0 := at_origin ha memQ
  have PM (k : ℕ) (hk : k≤4) : mu K k P=0 := paid_moment ho (by omega) (by omega) memP
  have QM (k : ℕ) (hk : k≤4) : mu K k Q=0 := paid_moment ho (by omega) (by omega) memQ
  have sh : diag (nodes A) (evalNodes A P)=evalNodes A (X*P) := by
    ext i
    simp
  let T : K[X] := X*P-Q
  have te : evalNodes A T=t-diag (nodes A) h := by
    have eq := congrArg (diag (nodes A)) hEq
    rw [map_add,sh,tEq] at eq
    simp only [T,map_sub]
    calc
      _ = (evalNodes A (X*P)+diag (nodes A) h)-evalNodes A Q-diag (nodes A) h := by abel
      _ = _ := by rw [←eq]; abel
  have tb : evalNodes A T∈B A U w (r+4) := by
    rw [te]
    exact (B A U w (r+4)).sub_mem (band_succ (r+3) ht) (band_move stable (by omega) hh)
  let a := T.coeff 7/G.coeff 7
  have dT : T.natDegree≤7 := by
    change (X*P-Q).natDegree ≤ 7
    have mulLe : (X*P).natDegree ≤ 7 := by
      apply (natDegree_mul_le (p := (X : K[X])) (q := P)).trans
      rw [natDegree_X]
      omega
    exact (natDegree_sub_le_of_le mulLe (e.trans (by decide : 6 ≤ 7))).trans (by decide)
  have gn : G≠0 := by intro ez; rw [ez,natDegree_zero] at Gd; omega
  have top : G.coeff 7≠0 := by
    rw [←Gd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr gn
  have aG : T.coeff 7=a*G.coeff 7 := (div_mul_cancel₀ _ top).symm
  have G4 : evalNodes A G∈B A U w (r+4) := band_succ (r+3) (band_succ (r+2) Gp)
  have vanishes : T-a • G=0 := chart_discards_polynomial ho H.treeNine (by
    rw [H.ranks.2.2.1]; omega) (deg_trim dT Gd.le aG) (by
    rw [map_sub,map_smul]
    exact (B A U w (r+4)).sub_mem tb ((B A U w (r+4)).smul_mem _ G4))
  by_contra out
  have pn : P≠0 := by
    intro z
    apply out
    simpa only [hEq,z,map_zero,zero_add] using hh
  have p6 : P.coeff 6≠0 := by
    intro hz
    have low : P.natDegree≤5 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_cases nn : n=6
      · simpa only [nn] using hz
      · exact coeff_eq_zero_of_natDegree_lt (d.trans_lt (by omega))
    exact pn (moment_band_detect (n:=4) low P0 (fun k=>PM _ (by have := k.isLt; omega)))
  let g := Q.coeff 6/P.coeff 6
  have rel : Q=g • P := by
    apply sub_eq_zero.mp
    have qg : Q.coeff 6=g*P.coeff 6 := (div_mul_cancel₀ _ p6).symm
    have low : (Q-g • P).natDegree≤5 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_cases nn : n=6
      · subst n
        simp only [coeff_sub,Polynomial.coeff_smul,smul_eq_mul,qg,sub_self]
      · rw [coeff_sub,Polynomial.coeff_smul,coeff_eq_zero_of_natDegree_lt (e.trans_lt (by omega)),
          coeff_eq_zero_of_natDegree_lt (d.trans_lt (by omega)),smul_zero,sub_zero]
    exact moment_band_detect (n:=4) low
      (by rw [eval_sub,eval_smul,Q0,P0,smul_zero,sub_zero])
      (fun k=>by rw [map_sub,map_smul,QM _ (by have := k.isLt; omega),
        PM _ (by have := k.isLt; omega),smul_zero,sub_zero])
  have relation : X*P=g • P+a • G := by
    have eq := sub_eq_zero.mp vanishes
    change X*P-Q=a • G at eq
    rw [rel] at eq
    exact (sub_eq_iff_eq_add.mp eq).trans (add_comm _ _)
  have recur (k : ℕ) (hk : k≤4) : mu K (k+1) P=0 := by
    have eq := congrArg (mu K k) relation
    have sh : mu K k (X*P)=mu K (k+1) P := by
      change (primitive (X^k*(X*P))).eval 1=(primitive (X^(k+1)*P)).eval 1
      rw [pow_succ,mul_assoc]
    rwa [sh,map_add,map_smul,map_smul,PM k hk,Gzero k (by omega),smul_zero,smul_zero,add_zero] at eq
  exact pn (moment_band_detect (n:=5) d P0 (fun k=>by
    have kb := k.isLt
    cases h : k.val with
    | zero => exact PM 0 (by decide)
    | succ t => simpa only [Nat.succ_eq_add_one] using recur t (by omega)))

/-- The degree-six polynomial band cannot hide a newly paid head power
inside E8. This does not assume F8 is exactly its paid head band. -/
theorem ordinary_E8_within_next_band (ho : HasOrder 13 A b)
    (H : OrdinaryStaircase A b G r U w)
    (hx : x∈treeSpace A 8) (hh : x∈chain (diag (nodes A)) U w (r+4)) :
    x∈chain (diag (nodes A)) U w (r+3) := by
  obtain ⟨P,y,d,hy,eq⟩ := chart_expand H.treeEight hx
  have rU := H.paidHead.head.baseRank
  rw [H.paidHead.five] at rU
  have hp : evalNodes A P∈B A U w (r+4) := by
    have q := (B A U w (r+4)).sub_mem hh (band_succ (r+3) hy)
    rwa [eq,add_sub_cancel_right] at q
  have z := chart_discards_polynomial ho H.treeNine (by rw [H.ranks.2.2.1]; omega) d hp
  simpa only [eq,z,map_zero,zero_add] using hy

theorem ordinary_grade_eight_clock_local (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G r U w) (hx : x∈zeroSpace A 8)
    {a : K} (localAt : ∀ i,nodes A i≠a → x i=0) : x∈U := by
  have stable := H.paidHead.head.coreStable
  have many := chart_growth_sites stable (by omega : 0<r+3) H.treeEight H.treeNine
    (by rw [H.ranks.2.1,H.ranks.2.2.1]; decide)
  have eq : diag (nodes A) x=a • x := by
    ext i
    by_cases e : nodes A i=a
    · simp [diag_apply,e]
    · simp [diag_apply,localAt i e]
  exact HeadFiber.localized_mem stable many
    (ordinary_adjacent_shift_pure ha ho seed H hx
      (by rw [eq]; exact (zeroSpace A 8).smul_mem _ hx)) localAt

set_option maxHeartbeats 850000 in
/-- A literal grade-three defect outside the ordinary invariant core
would act by a nonzero profile of degree at most three. No disjointness,
pointwise closure of U, or polynomial assumption on w is supplied. -/
theorem ordinary_grade_three_profile (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G r U w) {v : Fin 19→K}
    (hv : v∈zeroSpace A 3) (out : v∉U) :
    U.map (diag v)≤U ∧ ∃ P : K[X], P≠0 ∧ P.natDegree≤3 ∧
      v*w-weightedEval (nodes A) w P∈U := by
  have stable := H.paidHead.head.coreStable
  have bounds := H.paidHead.headBounds
  let c := nodes A
  let D := diag c
  have matU : U.map (diag v)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    have mask := clock_mask_invariant (fun x (hx : x∈U) => stable (Submodule.mem_map_of_mem hx))
    let g (a : K) := blockMask c a u*v
    have good (a : K) : g a∈U := by
      apply ordinary_grade_eight_clock_local ha ho seed H
        (zeroSpace_mul (m:=5) (n:=3) (H.paidHead.head.coreInside (mask a u hu)) hv) (a:=a)
      intro i nz
      simp [g,blockMask,nz]
    have eq : assembleBlocks c g=diag v u := by
      funext i
      rw [assembleBlocks_apply, diag_apply]
      change (blockMask c (c i) u) i * v i = v i * u i
      simp [blockMask, mul_comm]
    exact eq ▸ assembleBlocks_mem c mask g good
  have base : zeroSpace A 5=B A U w r := by simpa using H.paidHead.head.flags 0 (by decide)
  have vB : v∈B A U w r := base ▸ zeroSpace_mono A (by decide : 3≤5) hv
  have many := chart_growth_sites stable (by omega : 0<r+3) H.treeEight H.treeNine
    (by rw [H.ranks.2.1,H.ranks.2.2.1]; decide)
  have treeCredit (k : ℕ) (hk : k<r) : v*(D^k) w∈zeroSpace A 8 := by
    have hk' := ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp le_rfl).2 k hk
    change (D^k) w ∈ B A U w r at hk'
    rw [←base] at hk'
    exact zeroSpace_mul (m:=3) (n:=5) hv hk'
  have shift (k : ℕ) : D (v*(D^k) w)=v*(D^(k+1)) w := by
    ext i
    simp [D,diag_apply,pow_succ] <;> ring
  have earlier (k : ℕ) (hk : k+1<r) : v*(D^k) w∈B A U w (r+3) := by
    apply ordinary_adjacent_shift_pure ha ho seed H (treeCredit k (by omega))
    rw [show diag (nodes A) (v*(D^k) w)=_ from shift k]
    exact treeCredit (k+1) hk
  have all (k : ℕ) (hk : k<r) : v*(D^k) w∈B A U w (r+3) := by
    by_cases hn : k+1<r
    · exact earlier k hn
    · have phase := earlier (k-1) (by omega)
      have grown := band_move stable (by omega : 0<r+3) phase
      change D (v*(D^(k-1)) w)∈B A U w (r+4) at grown
      rw [shift,show k-1+1=k by omega] at grown
      exact ordinary_E8_within_next_band ho H (zeroSpace_le_treeSpace A 8 (treeCredit k hk)) grown
  obtain ⟨P,nz,d,e⟩ := HeadFiber.multiplier_profile_of_chart stable matU many
    (show 0<r by omega) all vB out
  exact ⟨matU,P,nz,by omega,e⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
