module

public import RKCert.ReviewedNative.ERKOrderTwelvePureExclusion
public import RKCert.ReviewedNative.RotatedClockProbe

public section

/-! # The order-twelve explicit stage bound over every characteristic-zero ring

The remaining nonzero-leak profile is ruled out by exact full-band
separation and one rotated native probe. Polynomial division with a
zero-at-one quotient replaces the earlier multiplicity count.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- The live part of a clock evaluation on a pointwise-closed
clock-invariant core is itself inside that core. -/
theorem core_supported_clock_profile {U : Submodule K (Fin (s+1) → K)}
    (stable : U.map (diag (nodes A))≤U)
    (closed : ∀ u∈U, ∀ v∈U, u*v∈U) {y : Fin (s+1) → K} (P : K[X])
    (core : ∀ i, LiveCore.live U i → y i=P.eval (nodes A i))
    (off : ∀ i, ¬LiveCore.live U i → y i=0) : y∈U := by
  classical
  obtain ⟨e,he,ind⟩ := LiveCore.exists_live_indicator U closed
  have eq : y=fun i => P.eval (nodes A i)*e i := by
    ext i
    by_cases hi : LiveCore.live U i
    · simp only [ind i,ite_eq_left hi,mul_one,core i hi]
    · simp only [ind i,ite_eq_right hi,mul_zero,off i hi]
  rw [eq]
  exact clock_function_mem (fun _ h => stable (Submodule.mem_map_of_mem h)) P.eval he

private theorem paid_weighted_head {U : Submodule K (Fin (s+1) → K)}
    {z : Fin (s+1) → K} {P : K[X]} {n : ℕ} (deg : P.natDegree<n) :
    weightedEval (nodes A) z P∈chain (diag (nodes A)) U z n := by
  let W := chain (diag (nodes A)) U z n
  have pay := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=z) n).mp le_rfl).2
  have eq (k : ℕ) (a : K) :
      weightedEval (nodes A) z (monomial k a)=a • (diag (nodes A)^k) z := by
    ext i
    simp [mul_assoc]
  rw [P.as_sum_range' n deg,map_sum]
  exact W.sum_mem (fun k hk => (eq k (P.coeff k)).symm ▸ W.smul_mem _ (pay k (Finset.mem_range.mp hk)))

private theorem head_rank_cap (D : (Fin (s+1) → K) →ₗ[K] (Fin (s+1) → K))
    (U : Submodule K (Fin (s+1) → K)) (z : Fin (s+1) → K) (n : ℕ) :
    finrank K (chain D U z n)≤finrank K U+n := by
  classical
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have e := Submodule.finrank_add_le_finrank_add_finrank (chain D U z n) (K ∙ (D^n) z)
    have one : finrank K (K ∙ (D^n) z)≤1 :=
      (finrank_span_le_card ({(D^n) z}:Set (Fin (s+1) → K))).trans (by simp)
    rw [chain]
    omega

private theorem RankTwoFourProfile.off_core_fit_mem
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) {P L : K[X]} (ld : L.natDegree≤6)
    (eq : ∀ i, ¬LiveCore.live U i → P.eval (nodes A i)=L.eval (nodes A i)*z i) :
    evalNodes A P∈chain (diag (nodes A)) U z 7 := by
  let W := chain (diag (nodes A)) U z 7
  let u := evalNodes A P-weightedEval (nodes A) z L
  have mem : u∈U := core_supported_clock_profile H.stable H.closed P
    (fun i hi => by simp only [u,Pi.sub_apply,evalNodes_apply,weightedEval_apply,H.disjoint i hi,mul_zero,sub_zero])
    (fun i hi => by simp only [u,Pi.sub_apply,evalNodes_apply,weightedEval_apply,eq i hi,sub_self])
  have iU : U≤W := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=z) 7).mp le_rfl).1
  have wl : weightedEval (nodes A) z L∈W := paid_weighted_head (by omega)
  simpa only [u,sub_add_cancel] using W.add_mem (iU mem) wl

private theorem RankTwoFourProfile.leak_in_eight
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) :
    evalNodes A (α • terminalLeak8)∈zeroSpace A 8 := by
  let c := nodes A
  let D := diag c
  let G := α • (terminalLeak8 : K[X])
  let y := evalNodes A G-z*z+weightedEval c z R
  have mem : y∈U := core_supported_clock_profile H.stable H.closed G
    (fun i hi => by
      simp only [y,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,evalNodes_apply,weightedEval_apply,
        H.disjoint i hi,mul_zero,add_zero,sub_zero])
    (fun i hi => by
      have sh := H.square i hi
      simp only [y,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,evalNodes_apply,weightedEval_apply,
        G,eval_smul,smul_eq_mul,c]
      linear_combination -sh)
  have step {n j : ℕ} (npos : 0<n) (sub : chain D U z n≤zeroSpace A j) :
      chain D U z (n+1)≤zeroSpace A (j+1) := by
    rw [←clock_chain_next H.stable npos]
    apply sup_le (sub.trans (zeroSpace_mono A (Nat.le_succ j)))
    rintro _ ⟨v,hv,rfl⟩
    exact diag_zeroSpace A j (sub hv)
  have h5 : chain D U z 5≤zeroSpace A 8 :=
    step (by decide) (step (by decide) H.sixth.ge)
  have w : weightedEval c z R∈zeroSpace A 8 :=
    h5 (paid_weighted_head (by have := H.rDegree; omega))
  have y8 := zeroSpace_mono A (by decide : 4≤8) (H.coreInside mem)
  have sq : z*z∈zeroSpace A 8 := zeroSpace_mul H.headInFour H.headInFour
  have e : y+z*z-weightedEval c z R=evalNodes A G := by dsimp [y]; abel
  exact e ▸ (zeroSpace A 8).sub_mem ((zeroSpace A 8).add_mem y8 sq) w

variable [CharZero K]

set_option maxHeartbeats 650000 in
/-- Exact full-band separation forces the observed nonzero- or zero-leak
relation to be an actual polynomial quotient with value zero at one. -/
theorem RankTwoFourProfile.anchored_quotient
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder A b 12) (S : Saturation A b)
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) :
    ∃ D : K[X], D.natDegree≤Q.natDegree ∧ D.eval 1=0 ∧
      (α • terminalLeak8)*Q=terminalMesh6*D := by
  classical
  let M := (terminalMesh6 : K[X])
  let G := α • (terminalLeak8 : K[X])
  have md : M.natDegree=6 := terminalMesh6_natDegree_eq
  have gd : G.natDegree≤6 := (natDegree_smul_le ..).trans terminalLeak8_degree
  obtain ⟨D,dd,one,pd⟩ := polynomial_degree_cut_at_one M (G*Q) (by decide) md
    (natDegree_mul_le.trans (Nat.add_le_add_right gd _))
  let P := G*Q-M*D
  let L := M-R*Q-Q*D
  have qd := H.qDegree
  have rd := H.rDegree
  have ld : L.natDegree≤6 :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le md.le (natDegree_mul_le.trans (by omega))))
      (natDegree_mul_le.trans (by omega)))
  have agree (i : Fin (s+1)) (off : ¬LiveCore.live U i) :
      P.eval (nodes A i)=L.eval (nodes A i)*z i := by
    have hM := H.mesh i off
    have hG := H.square i off
    have zt : coordinate (K:=K) (Fin.last s) i*z i=0 := by
      by_cases e : i=Fin.last s
      · subst i
        rw [H.lastZero,mul_zero]
      · simp [coordinate,e]
    have dt : coordinate (K:=K) (Fin.last s) i*D.eval (nodes A i)=0 := by
      by_cases e : i=Fin.last s
      · subst i
        rw [S.terminalClock,one,mul_zero]
      · simp [coordinate,e]
    simp only [P,L,M,G,eval_sub,eval_mul,eval_smul,smul_eq_mul]
    linear_combination -(D.eval (nodes A i)+z i)*hM-Q.eval (nodes A i)*hG-zt-dt
  have mem := H.off_core_fit_mem ld agree
  have rank : finrank K ↥((coeffEval A 6).range⊔chain (diag (nodes A)) U z 7)=6+1+10 := by
    change finrank K ↥(clockBand6 A⊔chain (diag (nodes A)) U z 7)=17
    rw [H.top,finrank_top,Module.finrank_fin_fun,S.size]
  have cap : finrank K (chain (diag (nodes A)) U z 7)≤10 := by
    have e := head_rank_cap (diag (nodes A)) U z 7
    rwa [H.coreRank] at e
  have pz : P=0 := polynomial_buffer_separated ha ho (by decide) cap rank pd mem
  exact ⟨D,dd,one,sub_eq_zero.mp pz⟩

private theorem terminal_mesh_flat_probes (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) :
    ∀ k≤4, probe A b k (evalNodes A terminalMesh6)=b (Fin.last s) := by
  intro k hk
  have h := probe_zeroSpace (k:=k) ho (by omega)
    (physical_terminal_mesh ha ho S)
  change probe A b k (coordinate (K:=K) (Fin.last s)-evalNodes A terminalMesh6)=0 at h
  have paid : probe A b k (coordinate (K:=K) (Fin.last s))=b (Fin.last s) := by
    change row _ (coordinate (Fin.last s))=_
    rw [row_coordinate,S.terminalClock,one_pow,mul_one]
  rw [map_sub,paid] at h
  exact (sub_eq_zero.mp h).symm

/-- The degree-six leak has its first nonzero probe at four. Five zero
probes would contradict native two-endpoint coefficient separation. -/
theorem RankTwoFourProfile.leak_probe_edge (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b)
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) (nz : α≠0) :
    (∀ k<4, probe A b k (evalNodes A (α • terminalLeak8))=0) ∧
      probe A b 4 (evalNodes A (α • terminalLeak8))≠0 := by
  let G := α • (terminalLeak8 : K[X])
  have f := H.leak_in_eight
  have early (k : ℕ) (hk : k<4) : probe A b k (evalNodes A G)=0 :=
    probe_zeroSpace ho (by omega) f
  refine ⟨early,fun last => ?_⟩
  have d : G.natDegree≤5+1 := (natDegree_smul_le ..).trans terminalLeak8_degree
  have end0 : evalNodes A G (Fin.last s)=0 := by
    rw [evalNodes_apply,S.terminalClock]
    simp only [G,eval_smul,terminalLeak8_value_one,smul_zero]
  have gz : G=0 :=
    polynomial_zero_of_endpoint_probes ha ho (n:=5) (by decide) S.terminalClock d
      (origin_zeroSpace ha 8 f) end0 (by
        intro k hk
        rcases Nat.eq_or_lt_of_le (show k≤4 by omega) with rfl|lt
        · exact last
        · exact early k lt)
  have l0 : (terminalLeak8 : K[X])≠0 := by
    intro l
    have e := congrArg (Polynomial.eval (2:K)) l
    rw [terminalLeak8_value,eval_zero] at e
    norm_num at e
  have nonzero : G≠0 := by
    rw [show G=α • (terminalLeak8 : K[X]) from rfl,Polynomial.smul_eq_C_mul]
    exact mul_ne_zero (C_ne_zero.mpr nz) l0
  exact nonzero gz

/-- There can be no genuine nonzero-leak order-twelve chart at width
seventeen. The quotient and its rotated probe already contradict, without
counting multiple roots or using any new scalar nonvanishing gate. -/
theorem exclude_nonzero_rank_two_four (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b)
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) (nz : α≠0) : False := by
  classical
  obtain ⟨D,dd,one,fit⟩ := H.anchored_quotient ha ho S
  obtain ⟨early,sharp⟩ := H.leak_probe_edge ha ho S nz
  have qz := rotated_probe_detects_quotient (α • terminalLeak8) terminalMesh6 Q D
    early sharp (terminal_mesh_flat_probes ha ho S) (H.qDegree.trans (by decide)) dd one fit
  have d := terminalMesh6_natDegree_eq (K:=K)
  have many := H.many
  have zero : (terminalMesh6 : K[X])=0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (HeadFiber.physicalSites (nodes A) z)
    · apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast (show (terminalMesh6 : K[X]).natDegree<
        (HeadFiber.physicalSites (nodes A) z).card by omega)
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have w := H.mesh_on_head (Finset.mem_filter.mp hi).2
      simpa only [qz,eval_zero,mul_zero] using w
  simp [zero] at d

end RKResearch.Certified.Graded.ERK12

namespace RKResearch
open Certified.Graded.ERK12
universe u

/-- A strict explicit Runge–Kutta tableau of reviewed order twelve has
at least eighteen stages over an arbitrary characteristic-zero field. -/
theorem HasOrder.erk_order_twelve_stages_field {K : Type*} [Field K] [CharZero K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b 12) (ha : ∀ i k, i≤k → A i k=0) : 18≤s := by
  by_contra! cap
  cases s with
  | zero =>
    have low := h.erk_grade_five_charZero_stages_field ha (by decide)
    omega
  | succ s =>
    have C : s+1≤17 := by omega
    have S := saturation_of_order ha h C
    obtain ⟨U,z,α,Q,R,H,nz⟩ := actual_nonzero_leak_profile_at_cap ha h C
    exact exclude_nonzero_rank_two_four ha h S H nz

/-- The same native eighteen-stage bound permits all characteristic-zero
commutative rings, including rings with zero divisors. -/
theorem HasOrder.erk_order_twelve_stages {R : Type u} [CommRing R] [CharZero R]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b 12) (ha : ∀ i k, i≤k → A i k=0) : 18≤s :=
  h.strict_lower_triangular_of_charZero_fields ha
    (fun _ _ _ _ _ ht ho => ho.erk_order_twelve_stages_field ht)

end RKResearch

