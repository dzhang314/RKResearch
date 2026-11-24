module

public import RKCert.Dirk15NonC2Cardinal

@[expose] public section

/-! # Genuine forward head columns and the one degree-eight relation -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

omit [CharZero K] in
def evaluateColumn (A : Fin 20→Fin 20→K) : K[X] →ₗ[K] Vec K 20 :=
  LinearMap.pi (fun i => leval (nodes A i))

omit [CharZero K] in
@[simp] theorem evaluateColumn_eq (P : K[X]) : evaluateColumn A P=evalNodes A P := rfl

omit [CharZero K] in
theorem evaluateColumn_clock (P : K[X]) :
    diag (nodes A) (evaluateColumn A P)=evaluateColumn A (X*P) := by
  ext i
  simp only [evaluateColumn_eq,diag_apply,evalNodes_apply,eval_mul,eval_X]

namespace Order15NonC2Head
variable (h : Order15NonC2Head A b)

def orbit (n : ℕ) : Submodule K (Vec K 20) :=
  chain (diag (nodes A)) (nonC2Ghosts A b) h.head n

omit [CharZero K] in
theorem orbit_mono {n m : ℕ} (l : n≤m) : h.orbit n≤h.orbit m := by
  apply (chain_le_iff _).mpr
  obtain ⟨e,p⟩ := (chain_le_iff (T:=diag (nodes A)) (U:=nonC2Ghosts A b)
    (w:=h.head) m).mp le_rfl
  exact ⟨e,fun k kl => p k (kl.trans_le l)⟩

omit [CharZero K] in
theorem orbit_step {n : ℕ} (pos : 0<n) :
    h.orbit n⊔(h.orbit n).map (diag (nodes A))=h.orbit (n+1) :=
  chain_sup_map h.core.2.1 pos

omit [CharZero K] in
theorem orbit_pure (j : ℕ) (lo : 7≤j) : h.orbit (j-3)≤zeroSpace A j := by
  have steps (n : ℕ) : h.orbit (4+n)≤zeroSpace A (7+n) := by
    induction n with
    | zero => exact (h.band 2 (by decide)).ge
    | succ n ih =>
      change h.orbit (4+n+1)≤zeroSpace A (7+n+1)
      rw [←h.orbit_step (by omega : 0<4+n)]
      apply sup_le (ih.trans (zeroSpace_mono A (by omega)))
      rintro _ ⟨v,hv,rfl⟩
      exact diag_zeroSpace A (7+n) (ih hv)
  have ht := steps (j-7)
  rwa [show 4+(j-7)=j-3 by omega,show 7+(j-7)=j by omega] at ht

omit [CharZero K] in
theorem orbit_last (H : Order15NonC2Chart A b) (n : ℕ) {v : Vec K 20}
    (hv : v∈h.orbit n) : v (Fin.last 19)=0 := by
  have lastU (z : Vec K 20) (hz : z∈nonC2Ghosts A b) : z (Fin.last 19)=0 :=
    mem_nonC2Ghosts.mp hz _ (Or.inl H.terminal.weight_ne)
  have hw : h.head∈zeroSpace A 7 := (h.band 2 (by decide)).ge
    (by
      have p := ((chain_le_iff (T:=diag (nodes A)) (U:=nonC2Ghosts A b)
        (w:=h.head) 4).mp le_rfl).2 0 (by decide)
      simpa only [pow_zero,one_apply_eq_self] using p)
  have le : h.orbit n≤LinearMap.ker (LinearMap.proj (Fin.last 19)) := by
    apply (chain_le_iff _).mpr
    refine ⟨fun z hz => lastU z hz,fun k _ => ?_⟩
    change ((diag (nodes A))^k) h.head (Fin.last 19)=0
    rw [Clock.pow_diag_apply,H.terminal_pure_zero _ hw,mul_zero]
  exact le hv

theorem actual_parts (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) {j : ℕ} (hl : 7≤j) (hu : j≤12)
    {x : Vec K 20} (hx : x∈treeSpace A j) :
    ∃ P : K[X],P.natDegree≤7 ∧ ∃ v∈h.orbit (j-3), x=evaluateColumn A P+v := by
  classical
  rw [order15_nonC2_full_flag ha ho hq h j hl hu] at hx
  obtain ⟨q,hq',v,hv,eq⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a,rfl⟩ := hq'
  let P : K[X] := ofFn (7+1) a
  have dP : P.natDegree≤7 := by
    have k := ofFn_natDegree_lt (by decide : 0<7+1) a
    change P.natDegree<7+1 at k
    omega
  refine ⟨P,dP,v,hv,?_⟩
  rw [evaluateColumn_eq,evalNodes_ofFn A 7 a]
  exact eq.symm

end Order15NonC2Head

omit [CharZero K] in
theorem one_sub_clock_degree : (1-X:K[X]).natDegree=1 := by
  rw [show (1-X:K[X])=-(X-C (1:K)) by simp,natDegree_neg,natDegree_X_sub_C]

omit [CharZero K] in
theorem one_sub_clock_ne : (1-X:K[X])≠0 := by
  intro e
  have h := one_sub_clock_degree (K:=K)
  rw [e,natDegree_zero] at h
  contradiction

/-- In the paid ordinary E11 head part, every scalar relation of degree
at most eight is a multiple of the true terminal Radau relation. -/
theorem order15_nonC2_scalar_reduces (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b)
    {P : K[X]} (dP : P.natDegree≤8) (hx : evaluateColumn A P∈h.orbit 8) :
    ∃ a : K,P=C a*((1-X)*(normalizedRightRadau7 : K[X])) := by
  let D := (1-X)*(normalizedRightRadau7 : K[X])
  have dn : D.natDegree=8 := by
    have no : (normalizedRightRadau7 : K[X])≠0 := fun e => by
      have d := normalizedRightRadau7_degree (K:=K)
      rw [e,natDegree_zero] at d
      contradiction
    change ((1-X)*(normalizedRightRadau7 : K[X])).natDegree=8
    rw [natDegree_mul one_sub_clock_ne no,one_sub_clock_degree,normalizedRightRadau7_degree]
  have lead : D.coeff 8≠0 := by
    rw [←dn,coeff_natDegree]
    apply leadingCoeff_ne_zero.mpr
    intro e
    rw [e,natDegree_zero] at dn
    contradiction
  let a := P.coeff 8/D.coeff 8
  let R := P-C a*D
  have r8 : R.natDegree≤8 :=
    (natDegree_sub_le _ _).trans (max_le dP ((natDegree_C_mul_le _ _).trans dn.le))
  have c8 : R.coeff 8=0 := by
    simp only [R,coeff_sub,coeff_C_mul,a,div_mul_cancel₀ _ lead,sub_self]
  have rd : R.natDegree≤7 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    by_cases e : k=8
    · rwa [e]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have dh : evaluateColumn A D∈h.orbit 8 := h.orbit_mono (by decide : 5≤8)
    (order15_nonC2_radau_reduction ha ho hq h)
  have Rh : evaluateColumn A R∈h.orbit 8 := by
    change evaluateColumn A (P-C a*D)∈h.orbit 8
    rw [←smul_eq_C_mul,map_sub,map_smul]
    exact (h.orbit 8).sub_mem hx ((h.orbit 8).smul_mem a dh)
  have rs : evaluateColumn A R∈ordinaryScalarBand A := by
    refine ⟨fun j => R.coeff j.val,?_⟩
    rw [evaluateColumn_eq,evalNodes_eq_polyEval A _ rd]
  have dis := (order15_nonC2_full_flag_dim_split ha ho hq h 11 (by decide) (by decide)).1
  have v0 : evalNodes A R=0 := by
    have e : evaluateColumn A R∈ordinaryScalarBand A⊓h.orbit 8 := ⟨rs,Rh⟩
    change Disjoint (ordinaryScalarBand A) (h.orbit 8) at dis
    rw [dis.eq_bot,Submodule.mem_bot] at e
    exact e
  have coeff0 := poly_separated ho (by decide : 2*7+1≤15) (fun j => R.coeff j.val) (by
    rw [←evalNodes_eq_polyEval A _ rd,v0]
    exact (zeroSpace A 7).zero_mem)
  have r0 : R=0 := by
    ext j
    rw [coeff_zero]
    by_cases k : j<8
    · exact congrFun coeff0 ⟨j,k⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact ⟨a,sub_eq_zero.mp r0⟩

/-- Every extra scalar attached to an actual grade-j pure feature has
zero mixed moments across exactly the paid budget. -/
theorem scalar_pure_unit_pair (ho : HasTreeOrderAtLeast A b 15) {j : ℕ}
    {P Q : K[X]} (dP : P.natDegree≤j)
    (pure : evalNodes A P∈zeroSpace A j) (pay : j+Q.natDegree+1≤15) :
    unitIntegral (P*Q)=0 := by
  have tr : OrdinaryTrace A j (evalNodes A P) 0 := by
    refine ⟨by simp,?_⟩
    have eq : evalNodes A (0:K[X])=0 := by ext i; simp
    simpa only [eq,sub_zero] using pure
  have a := tr.pair_polynomial ho Q pay
  have b := (OrdinaryTrace.scalar A dP).pair_polynomial ho Q pay
  rw [unitIntegral_apply,←b,a,zero_mul]
  simp [formalPrimitive]

end
end RKCert.Paired
