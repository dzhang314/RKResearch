module

public import RKCert.ReviewedNative.ERK13NativePencilFactorTrace
public import RKCert.ReviewedNative.ERK13NativePencilSquare
public import RKCert.ReviewedNative.ERK13NativePencilProjection
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section
/-! # Both genuinely preterminal knots after the clean square factors -/
namespace RKResearch.Certified.Graded.ERK13NativePencil
open ERK13NativeFirst RKResearch Polynomial Reverse Module NativeLobatto MarkedAdjacent
open RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b w v : Fin 19→K} {r : ℕ}
variable {U : Submodule K (Fin 19→K)} {G R Q P : K[X]}
set_option maxHeartbeats 1800000

structure PencilFactor (A : Matrix (Fin 19) (Fin 19) K) (U : Submodule K (Fin 19→K))
    (v : Fin 19→K) (G R Q : K[X]) : Prop where
  rn : R≠0
  factor : G=R*Q
  amp : ∀ i,v i≠0 → v i=R.eval (nodes A i)
  mesh : ∃ u∈U,evalNodes A G=u+weightedEval (nodes A) v Q+G.eval 1 • coordinate (Fin.last 18)

theorem PencilSquareSection.factor_of_low (L : PencilSquareSection A b U w v G P R Q)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (low : (G-R*Q).coeff 7=0) :
    PencilFactor A U v G R Q ∧ R.natDegree=4 ∧ Q.natDegree=3 := by
  obtain ⟨alpha,beta,E⟩ := L.head.original.early_degree_seven_pencil_data ha ho (width19_pays_terminal_by_seven ha ho)
  have dg : G.natDegree=7 := L.head.original.first.degree
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at dg; omega
  have qnz := L.q_ne_of_low low
  have pz := pencil_small_square_projection_zero E dg L.pd L.p0 L.paid L.qd qnz (L.divides_of_low_delta low)
  obtain ⟨u,hu,form⟩ := L.square
  rw [pz,map_zero,zero_add,eval_zero,zero_smul,sub_zero] at form
  have amp (i : Fin 19) (vi : v i≠0) : v i=R.eval (nodes A i) := by
    have uz : u i=0 := by by_contra ne; exact vi (L.head.clean i ⟨u,hu,ne⟩)
    have e := congrFun form i
    simp only [Pi.mul_apply,Pi.add_apply,weightedEval_apply,uz,add_zero] at e
    exact mul_right_cancel₀ vi e
  have ddelta := natDegree_cap_of_zero_top (n:=6) L.delta_cap low
  let V := HeadFiber.physicalSites (nodes A) v
  have many : 6 < V.card := L.head.more_physical_clocks ha ho
  have δz : G-R*Q=0 := by
    apply eq_of_degrees_lt_of_eval_finset_eq V
    · exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (show (G-R*Q).natDegree<V.card by omega))
    · simp
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have vi := (Finset.mem_filter.mp hi).2
      obtain ⟨f,hf,m⟩ := L.mesh
      have ui : f i=0 := by by_contra ne; exact vi (L.head.clean i ⟨f,hf,ne⟩)
      have iL : i≠Fin.last 18 := fun eq=>vi (eq.symm ▸ L.head.headLast)
      have h := congrFun m i
      simp only [evalNodes_apply,Pi.add_apply,weightedEval_apply,Pi.smul_apply,smul_eq_mul,ui,
        zero_add,coordinate_last_apply_zero iL,mul_zero,add_zero,amp i vi] at h
      rw [eval_sub,eval_mul,eval_zero,h,sub_eq_zero,mul_comm]
  have fac := sub_eq_zero.mp δz
  have rn : R≠0 := by intro z; exact gn (by rw [fac,z,zero_mul])
  rw [fac,natDegree_mul rn qnz] at dg
  have rd := L.rd
  have qd := L.qd
  exact ⟨⟨rn,fac,amp,L.mesh⟩,by omega,by omega⟩

private theorem overlap_of_factor {alpha beta : K} (E : NativeEarlyPencilData b G alpha beta)
    (dg : G.natDegree=7) {N T : K[X]} (nn : N≠0) (nd : N.natDegree≤5)
    (eq : G*T=N*P) : ¬IsCoprime (pencilB alpha beta) P :=
  not_coprime_of_degree_seven_overlap dg (pencil_data_factor E) nn nd eq

theorem cubic_factor_impossible (S : PencilCleanHead A b 3 U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (gate : CubicPencilCut K)
    (F : PencilFactor A U v G R Q) (rd : R.natDegree≤3) (qd : Q.natDegree≤4) : False := by
  obtain ⟨e,he,em⟩ := LiveCore.exists_live_indicator U S.coreClosed
  have B := cubic_budget S ho rd
  have piv := factor_pivot S ha ho B he em F.rn F.factor F.amp F.mesh
  obtain ⟨k,K₁⟩ := piv X X_ne_zero (by simp) (by simp)
  let t := nodes A k
  let N : K[X] := X*(X-C t)
  have nd : N.natDegree≤2 := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) (show (X-C t).natDegree≤1 by simp)
  have nn : N≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)
  obtain ⟨l,K₂⟩ := piv N nn (nd.trans (by decide)) (by simp [N])
  let u := nodes A l
  have tn : t≠0 := by simpa only [eval_X] using K₁.maskNonzero
  have split : u*(u-t)≠0 := by simpa only [N,u,eval_mul,eval_X,eval_sub,eval_C] using K₂.maskNonzero
  obtain ⟨un,ut⟩ := mul_ne_zero_iff.mp split
  obtain ⟨s,trace⟩ := shared_factor_trace (Q:=Q) S ha ho he B
  have a (T : K[X]) (d : (T*X).natDegree≤3) :
      (primitive ((T*X)*R)).eval t=(s*(T*X).coeff 3)*radauValue t :=
    trace X T k K₁ d (by simp)
  have c (T : K[X]) (d : (T*N).natDegree≤3) :
      (primitive ((T*N)*R)).eval u=(s*(T*N).coeff 3)*radauValue u :=
    trace N T l K₂ d (by simp [N])
  have self2 : (X:K[X])*X=X^2 := (pow_two X).symm
  have self3 : (X:K[X])^2*X=X^3 := (pow_succ X 2).symm
  have t1 := a 1 (by simp)
  have t2 := a X (by simp [self2])
  have t3 := a (X^2) (by simp [self3])
  have u2 := c 1 (by simpa only [one_mul] using nd.trans (by decide : 2≤3))
  have u3 := c X (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) nd)
  have f2 : N*R=X^2*R-t • (X*R) := by dsimp only [N]; rw [smul_eq_C_mul]; ring
  have f3 : (X*N)*R=X^3*R-t • (X^2*R) := by dsimp only [N]; rw [smul_eq_C_mul]; ring
  have nc : N.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have xc : (X*N).coeff 3=1 := by
    have eq : X*N=X^3-t • (X^2:K[X]) := by dsimp only [N]; rw [Polynomial.smul_eq_C_mul]; ring
    rw [eq,coeff_sub,Polynomial.coeff_smul]
    simp [coeff_X_pow]
  have gr (i : Fin 19) (z : Q.eval (nodes A i)=0) : G.eval (nodes A i)=0 := by rw [F.factor,eval_mul,z,mul_zero]
  have D : NativeMarkedCubicPortPair A G R (earlyRadauMode K) s k l := by
    refine ⟨lt_of_le_of_ne (Fin.le_last k) K₁.notLast,lt_of_le_of_ne (Fin.le_last l) K₂.notLast,
      tn,un,(sub_ne_zero.mp ut).symm,gr k K₁.complementZero,gr l K₂.complementZero,?_,?_,?_,?_,?_⟩
    · simpa [coeff_X] using t1
    · simpa [self2,coeff_X_pow] using t2
    · simpa [self3,coeff_X_pow,earlyRadauMode_eval,t] using t3
    · simpa only [one_mul,f2,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,nc,mul_zero,zero_mul] using u2
    · simpa only [f3,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,xc,mul_one,earlyRadauMode_eval,u] using u3
  have early := width19_pays_terminal_by_seven ha ho
  obtain ⟨a,beta,E⟩ := S.original.early_degree_seven_pencil_data ha ho early
  have gd : G.natDegree=7 := S.original.first.degree
  have qn : Q≠0 := by intro z; rw [F.factor,z,mul_zero,natDegree_zero] at gd; omega
  exact overlap_of_factor (P:=R) E gd qn (qd.trans (by decide)) (T:=1) (by rw [mul_one,F.factor,mul_comm])
    (actual_cubic_ports_coprime gate E F.rn rd D ⟨s,fun x=>by rw [earlyRadauMode_eval]⟩)

end
end RKResearch.Certified.Graded.ERK13NativePencil
