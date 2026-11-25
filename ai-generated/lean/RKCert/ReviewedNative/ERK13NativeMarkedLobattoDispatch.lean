module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoTerminal
public import RKCert.ReviewedNative.NativeLobattoPurePort

@[expose] public section

/-! # Scalar discharge of the complete degree-six marked fork

Only this small leaf waits for the integral complementary-factor
certificate. The geometry and its causal dispatch can be verified
independently through the exact first-port premise. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w : Fin 19→K} {r : ℕ} {G : K[X]}

theorem earlyLobattoMesh_eq_integral :
    earlyLobattoMesh K=NativeLobatto.lobattoMesh.map (algebraMap ℤ K) := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  rw [earlyLobattoMesh_eval,NativeLobatto.lobattoMesh,Polynomial.map_mul,Polynomial.map_X,
    eval_mul,eval_X,NativeLobatto.eval_map_lobattoQuintic]

theorem lobatto_pure_first_cut : LobattoPureFirstCut K := by
  intro R Q g gn _ h t tn ht
  rw [earlyLobattoMesh_eq_integral,smul_eq_C_mul] at h
  exact NativeLobatto.primitive_X_ne_zero_of_lobatto_factor R Q g gn h t tn ht

theorem NativeMarkedEscapeChart.degree_six_impossible
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : False :=
  H.degree_six_impossible_of_cut ha ho (lobatto_pure_first_cut (K:=K))

theorem no_marked_first_escape_degree_six
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (paid : NativePaidHead A b r U w) (first : FirstEscape A b 5 G) : False :=
  no_marked_first_escape_degree_six_of_cut ha ho seed paid first (lobatto_pure_first_cut (K:=K))

end
end RKResearch.Certified.Graded.ERK13NativeFirst
