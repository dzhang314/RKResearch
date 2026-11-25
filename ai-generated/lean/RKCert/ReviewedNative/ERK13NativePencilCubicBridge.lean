module

public import RKCert.ReviewedNative.ERK13NativeMarkedPencilOverlap
public import RKCert.ReviewedNative.ERK13NativeMarkedPencilEndpoint
public import RKCert.ReviewedNative.ERK13NativePencilHead
public import RKCert.ReviewedNative.ERK13NativeWidth19EndpointOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The five scalar primitive equations on the actual a=6 stage knots

The radius bound is obtained upstream from real original rows; no
polynomial profile, overlap, or ratio of endpoint modes is presumed. -/
namespace RKResearch.Certified.Graded.ERK13NativePencil
open ERK13NativeFirst RKResearch Polynomial Reverse Module NativeLobatto
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w : Fin 19→K} {r : ℕ}
variable {G P J : K[X]} {alpha beta scale : K} {k l : Fin 19}

def pencilB (a b : K) : K[X] := C a*radauQuotient X+C b*lobattoValue X
def pencilMoment (P : K[X]) (n : ℕ) (x : K) := (primitive (X^n*P)).eval x

/-- Precisely the proved scalar API of NativePencilFivePrimitive. Separating it
as a quantified scalar proposition leaves every physical step independently auditable. -/
def CubicPencilCut (K : Type*) [Field K] : Prop :=
  ∀ (P : K[X]), P.natDegree≤3 → P≠0 → ∀ a b k t z : K,
  b≠0 → t≠0 → z≠0 → z≠1 →
  a*radauQuotient t+b*lobattoValue t=0 →
  a*radauQuotient (t*z)+b*lobattoValue (t*z)=0 →
  pencilMoment P 1 t=0 → pencilMoment P 2 t=0 → pencilMoment P 3 t=k*radauValue t →
  pencilMoment P 2 (t*z)-t*pencilMoment P 1 (t*z)=0 →
  pencilMoment P 3 (t*z)-t*pencilMoment P 2 (t*z)=k*radauValue (t*z) →
  IsCoprime (pencilB a b) P

theorem pencil_data_eval (E : NativeEarlyPencilData b G alpha beta) (x : K) :
    G.eval x=x*(alpha*radauQuotient x+beta*lobattoValue x) := by
  rw [E.chart,eval_add,eval_smul,eval_smul,earlyRadauMode_eval,earlyLobattoMesh_eval]
  simp only [smul_eq_mul,radauValue]
  ring

theorem pencil_data_factor (E : NativeEarlyPencilData b G alpha beta) :
    G=X*pencilB alpha beta := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  rw [pencil_data_eval E,eval_mul,eval_X,pencilB]
  simp [radauQuotient,lobattoValue] <;> ring

theorem normalized_leakage {r : ℕ} {w : Fin 19→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (mode : J=0 ∨ NativeEarlyF7Mode A U w r J) (scale : K) :
    ∃ s : K, ∀ x : K,scale*J.eval x=s*radauValue x := by
  rcases mode with h|h
  · exact ⟨0,fun x=>by simp [h]⟩
  · exact ⟨scale,fun x=>by rw [h.eval_eq_radauValue ha ho (width19_last_node_clean_six ha ho).1]⟩

theorem actual_cubic_ports_coprime (gate : CubicPencilCut K) (E : NativeEarlyPencilData b G alpha beta)
    (pn : P≠0) (pd : P.natDegree≤3) (D : NativeMarkedCubicPortPair A G P J scale k l)
    (shared : ∃ s : K,∀x,scale*J.eval x=s*radauValue x) :
    IsCoprime (pencilB alpha beta) P := by
  let t := nodes A k
  let u := nodes A l
  let z := u/t
  have tn : t≠0 := D.firstNonzero
  have un : u≠0 := D.secondNonzero
  have zn : z≠0 := div_ne_zero un tn
  have tz : t*z=u := by dsimp [z]; field_simp [tn] <;> ring
  have zone : z≠1 := by
    intro h
    apply D.distinct
    simpa only [h,mul_one] using tz
  have root {x : K} (nx : x≠0) (gx : G.eval x=0) : alpha*radauQuotient x+beta*lobattoValue x=0 :=
    (mul_eq_zero.mp ((pencil_data_eval E x).symm.trans gx)).resolve_left nx
  obtain ⟨s,share⟩ := shared
  apply gate P pd pn alpha beta s t z E.lobattoNonzero tn zn zone
    (root tn D.firstMesh) (by rw [tz]; exact root un D.secondMesh)
  · simpa only [pencilMoment,pow_one] using D.firstLinear
  · exact D.firstQuadratic
  · exact D.firstCubic.trans (share t)
  · rw [tz]
    simpa only [pencilMoment,pow_one] using D.secondQuadratic
  · rw [tz]
    exact D.secondCubic.trans (share u)

theorem grade_three_core_pencil (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (gate : CubicPencilCut K) : zeroSpace A 3≤U := by
  have early := width19_pays_terminal_by_seven ha ho
  obtain ⟨a,d,E⟩ := H.early_degree_seven_pencil_data ha ho early
  intro v hv
  by_contra off
  obtain ⟨P,J,s,k,l,pn,pd,mode,D,overlap⟩ := H.early_pencil_ports_with_overlap ha ho early hv off
  exact overlap _ (pencil_data_factor E)
    (actual_cubic_ports_coprime gate E pn pd D (normalized_leakage ha ho mode s))

theorem ranks_of_pencil_chart (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (gate : CubicPencilCut K) :
    finrank K (zeroSpace A 4)=4 ∧ (r=2 ∨ r=3) ∧
      (r=3 → zeroSpace A 3=U ∧ finrank K U=2) :=
  rank_radius_of_three_in_core ha ho H.head (grade_three_core_pencil H ha ho gate)

end
end RKResearch.Certified.Graded.ERK13NativePencil
