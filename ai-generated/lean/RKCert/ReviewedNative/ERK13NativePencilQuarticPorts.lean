module
public import RKCert.ReviewedNative.ERK13NativePencilFactorPorts
public import RKCert.ReviewedNative.ERK13NativePencilTerminal
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section
/-! # All real degree-seven first-escape charts reduce to two scalar inputs

The only quartic scalar premise contains three original primitive values
and true nonzero distinct field knots, not any tableau incidence. -/
namespace RKResearch.Certified.Graded.ERK13NativePencil
open ERK13NativeFirst RKResearch Polynomial Reverse Module NativeLobatto MarkedAdjacent
open RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b w v : Fin 19→K} {r : ℕ}
variable {U : Submodule K (Fin 19→K)} {G R Q : K[X]}
set_option maxHeartbeats 2000000

def QuarticPencilCut (K : Type*) [Field K] : Prop :=
  ∀ (a b s t u : K) (R Q : K[X]), a≠0 → b≠0 → t≠0 → u≠0 → t≠u →
    R.natDegree=4 → Q.natDegree=3 → R.eval 0≠0 →
    X*pencilB a b=R*Q → Q.eval 0=0 → Q.eval t=0 → Q.eval u=0 →
    pencilMoment R 1 t=0 → pencilMoment R 2 t=s*radauValue t →
    pencilMoment R 2 u-t*pencilMoment R 1 u=s*radauValue u → False

private theorem quartic_zero_factor_impossible (S : PencilCleanHead A b r U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (gate : CubicPencilCut K)
    (F : PencilFactor A U v G R Q) (rd : R.natDegree=4) (qd : Q.natDegree=3) (rz : R.eval 0=0) : False := by
  obtain ⟨P,rp⟩ := X_dvd_iff.mpr (show R.coeff 0=0 by rw [coeff_zero_eq_eval_zero]; exact rz)
  have pn : P≠0 := by intro z; exact F.rn (by rw [rp,z,mul_zero])
  have pd : P.natDegree≤3 := by rw [rp,natDegree_X_mul pn] at rd; omega
  obtain ⟨e,he,em⟩ := LiveCore.exists_live_indicator U S.coreClosed
  have B := quartic_budget S ho rd.le
  have piv := factor_pivot S ha ho B he em F.rn F.factor F.amp F.mesh
  obtain ⟨k,K₁⟩ := piv 1 one_ne_zero (by simp) (fun h=>by omega)
  let t := nodes A k
  let N : K[X] := X-C t
  have nd : N.natDegree≤1 := by simp [N]
  obtain ⟨l,K₂⟩ := piv N (X_sub_C_ne_zero t) (nd.trans (by decide)) (fun h=>by omega)
  let u := nodes A l
  have nz {j : Fin 19} (h : R.eval (nodes A j)≠0) : nodes A j≠0 := fun y=>h (by rw [y,rz])
  have tn : t≠0 := nz K₁.factorNonzero
  have un : u≠0 := nz K₂.factorNonzero
  have ut : u-t≠0 := by simpa only [N,u,eval_sub,eval_X,eval_C] using K₂.maskNonzero
  obtain ⟨s,trace⟩ := shared_factor_trace (Q:=Q) S ha ho he B
  have a (T : K[X]) (d : T.natDegree≤2) :
      (primitive (T*R)).eval t=(s*T.coeff 2)*radauValue t := by
    simpa only [mul_one] using trace 1 T k K₁ (by simpa only [mul_one] using d) (fun h=>by omega)
  have c (T : K[X]) (d : (T*N).natDegree≤2) :
      (primitive ((T*N)*R)).eval u=(s*(T*N).coeff 2)*radauValue u :=
    trace N T l K₂ d (fun h=>by omega)
  have t1 := a 1 (by simp)
  have t2 := a X (by simp)
  have t3 := a (X^2) (by simp)
  have u2 := c 1 (by simpa only [one_mul] using nd.trans (by decide : 1≤2))
  have u3 := c X (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) nd)
  have f1 : X*R=X^2*P := by rw [rp]; ring
  have f1' : X^2*R=X^3*P := by rw [rp]; ring
  have f2 : N*R=X^2*P-t • (X*P) := by dsimp only [N]; rw [rp,smul_eq_C_mul]; ring
  have f3 : (X*N)*R=X^3*P-t • (X^2*P) := by dsimp only [N]; rw [rp,smul_eq_C_mul]; ring
  have nc : N.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have xc : (X*N).coeff 2=1 := by
    have eq : X*N=X^2-t • (X:K[X]) := by dsimp only [N]; rw [Polynomial.smul_eq_C_mul]; ring
    rw [eq,coeff_sub,Polynomial.coeff_smul]
    simp [coeff_X_pow,coeff_X]
  have gr (i : Fin 19) (z : Q.eval (nodes A i)=0) : G.eval (nodes A i)=0 := by rw [F.factor,eval_mul,z,mul_zero]
  have D : NativeMarkedCubicPortPair A G P (earlyRadauMode K) s k l := by
    refine ⟨lt_of_le_of_ne (Fin.le_last k) K₁.notLast,lt_of_le_of_ne (Fin.le_last l) K₂.notLast,
      tn,un,(sub_ne_zero.mp ut).symm,gr k K₁.complementZero,gr l K₂.complementZero,?_,?_,?_,?_,?_⟩
    · have c₁ : (1:K[X]).coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by simp)
      simpa only [one_mul,rp,c₁,mul_zero,zero_mul,t] using t1
    · simpa [f1,coeff_X] using t2
    · simpa [f1',coeff_X_pow,earlyRadauMode_eval,t] using t3
    · simpa only [one_mul,f2,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,nc,mul_zero,zero_mul] using u2
    · simpa only [f3,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,xc,mul_one,earlyRadauMode_eval,u] using u3
  obtain ⟨a,beta,E⟩ := S.original.early_degree_seven_pencil_data ha ho (width19_pays_terminal_by_seven ha ho)
  have dg : G.natDegree=7 := S.original.first.degree
  have qn : Q≠0 := by intro z; rw [z,natDegree_zero] at qd; omega
  have nd : (X*Q).natDegree≤5 := by rw [natDegree_X_mul qn,qd]; decide
  have ov := not_coprime_of_degree_seven_overlap (P:=P) (T:=1) dg (pencil_data_factor E)
    (mul_ne_zero X_ne_zero qn) nd (by rw [mul_one,F.factor,rp]; ring)
  exact ov (actual_cubic_ports_coprime gate E pn pd D ⟨s,fun x=>by rw [earlyRadauMode_eval]⟩)

private theorem quartic_nonzero_factor_impossible (S : PencilCleanHead A b r U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (cut : QuarticPencilCut K)
    (F : PencilFactor A U v G R Q) (rd : R.natDegree=4) (qd : Q.natDegree=3) (rz : R.eval 0≠0) : False := by
  obtain ⟨e,he,em⟩ := LiveCore.exists_live_indicator U S.coreClosed
  have B := quartic_budget S ho rd.le
  have piv := factor_pivot S ha ho B he em F.rn F.factor F.amp F.mesh
  obtain ⟨k,K₁⟩ := piv X X_ne_zero (by simp) (fun h=>by omega)
  let t := nodes A k
  let N : K[X] := X*(X-C t)
  have nd : N.natDegree≤2 := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) (show (X-C t).natDegree≤1 by simp)
  obtain ⟨l,K₂⟩ := piv N (mul_ne_zero X_ne_zero (X_sub_C_ne_zero t)) nd (fun h=>by omega)
  let u := nodes A l
  have tn : t≠0 := by simpa only [eval_X] using K₁.maskNonzero
  have split : u*(u-t)≠0 := by simpa only [N,u,eval_mul,eval_X,eval_sub,eval_C] using K₂.maskNonzero
  obtain ⟨un,ut⟩ := mul_ne_zero_iff.mp split
  obtain ⟨s,trace⟩ := shared_factor_trace (Q:=Q) S ha ho he B
  have t1 := trace X 1 k K₁ (by simp) (fun h=>by omega)
  have t2 := trace X X k K₁ (by simp [←pow_two]) (fun h=>by omega)
  have u2 := trace N 1 l K₂ (by simpa only [one_mul] using nd) (fun h=>by omega)
  have f2 : N*R=X^2*R-t • (X*R) := by dsimp only [N]; rw [smul_eq_C_mul]; ring
  have nc : N.coeff 2=1 := by
    have eq : N=X^2-t • (X:K[X]) := by dsimp only [N]; rw [Polynomial.smul_eq_C_mul]; ring
    rw [eq,coeff_sub,Polynomial.coeff_smul]
    simp [coeff_X_pow,coeff_X]
  obtain ⟨a,beta,E⟩ := S.original.early_degree_seven_pencil_data ha ho (width19_pays_terminal_by_seven ha ho)
  have fac := (pencil_data_factor E).symm.trans F.factor
  have qz : Q.eval 0=0 := by
    have y := congrArg (fun W : K[X]=>W.eval 0) fac
    simp only [eval_mul,eval_X,zero_mul] at y
    exact (mul_eq_zero.mp y.symm).resolve_left rz
  apply cut a beta s t u R Q E.radauNonzero E.lobattoNonzero tn un (sub_ne_zero.mp ut).symm rd qd rz
    fac qz K₁.complementZero K₂.complementZero
  · simpa [pencilMoment,coeff_X] using t1
  · simpa [pencilMoment,←pow_two,coeff_X_pow] using t2
  · simpa only [one_mul,f2,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,nc,mul_one,
      pencilMoment,pow_one,u] using u2

theorem early_pencil_impossible_of_scalar_ports (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (cubic : CubicPencilCut K) (quartic : QuarticPencilCut K) : False := by
  obtain ⟨four,rad,_⟩ := ranks_of_pencil_chart H ha ho cubic
  obtain ⟨v,S⟩ := clean_pencil_head H ha ho four
  rcases rad with two | three
  · subst r
    obtain ⟨P,R,Q,Z⟩ := S.radius_two_square_section ha ho
    by_cases low : (G-R*Q).coeff 7=0
    · obtain ⟨F,rd,qd⟩ := Z.factor_of_low ha ho low
      by_cases rz : R.eval 0=0
      · exact quartic_zero_factor_impossible S ha ho cubic F rd qd rz
      · exact quartic_nonzero_factor_impossible S ha ho quartic F rd qd rz
    · exact Z.impossible_of_high_delta ha ho low
  · subst r
    obtain ⟨R,Q,rn,rd,qd,fac,amp,mesh⟩ := S.radius_three_factor ha ho
    exact cubic_factor_impossible S ha ho cubic ⟨rn,fac,amp,mesh⟩ rd qd

theorem no_marked_first_escape_degree_seven_of_scalar_ports
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (paid : NativePaidHead A b r U w) (first : FirstEscape A b 6 G)
    (cubic : CubicPencilCut K) (quartic : QuarticPencilCut K) : False :=
  early_pencil_impossible_of_scalar_ports (native_marked_escape_chart ha ho seed paid first) ha ho cubic quartic

end
end RKResearch.Certified.Graded.ERK13NativePencil
