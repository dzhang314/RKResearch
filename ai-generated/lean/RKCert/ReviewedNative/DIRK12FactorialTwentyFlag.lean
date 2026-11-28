module

public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagChecks
public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagProducts
public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagActionsEarly
public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagActionsLate
import Mathlib.Tactic.Ring

@[expose] public section

/-! The literal width-20 DIRK12 by integer structural flags and one
integer Bézout identity for the thirteenth bush and one mixed defect. -/
namespace RKResearch.Certified.DIRK12FactorialTwentyFlag

open RKResearch ScaledIntegerFlagReplay FiniteRootedTree
open scoped Matrix
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false


private theorem actionA (k : Nat) (hk : k+1<12) (i : Fin (packet.size k)) :
    checkA packet k i=true := by
  have h : blockA k=true := by
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact actA0
    · exact actA1
    · exact actA2
    · exact actA3
    · exact actA4
    · exact actA5
    · exact actA6
    · exact actA7
    · exact actA8
    · exact actA9
    · exact actA10
  exact List.all_eq_true.mp h i (List.mem_finRange i)

private theorem actionC (k : Nat) (hk : k+1<12) (i : Fin (packet.size k)) :
    checkC packet k i=true := by
  have h : blockC k=true := by
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact actC0
    · exact actC1
    · exact actC2
    · exact actC3
    · exact actC4
    · exact actC5
    · exact actC6
    · exact actC7
    · exact actC8
    · exact actC9
    · exact actC10
  exact List.all_eq_true.mp h i (List.mem_finRange i)

theorem receipts : Receipts 12 packet where
  stage_ne := check_D_pos
  weight_ne := check_D_pos
  scale_ne := scale_nonzero
  node := node_checked
  stepA := actionA
  stepC := actionC
  product := product_receipt
  primitive := primitive_checked
  silent := silent_checked
  scalar := scalar_receipt

theorem rational_order12 : HasOrder 12 (A packet) (b packet) := order receipts

def bush13 : FiniteRootedTree := bushyTree 13
def mixed13 : FiniteRootedTree := .butcherProduct (bushyTree 4) (bushyTree 9)

def integerDefect (t : FiniteRootedTree) : ℤ :=
  (t.factorial:ℤ)*(packet.w ⬝ᵥ Φ t (matrix packet))-D^13

theorem integer_bush_scaled :
    (161663040:ℤ)*integerDefect bush13=97351*D^13 := by
  unfold integerDefect bush13
  rw [Φ_bushyTree]
  change (161663040:ℤ)*((13:ℤ)*(packet.w ⬝ᵥ ((matrix packet) *ᵥ (1:VI 20))^12)-
    D^13)=97351*D^13
  rw [←act_eq,eq_of_eqV node_checked,←output_eq]
  exact raw_bush_checked

theorem integer_mixed_scaled :
    (95800320:ℤ)*integerDefect mixed13=(-281923)*D^13 := by
  unfold integerDefect mixed13
  rw [Φ,Φ_bushyTree,Φ_bushyTree]
  change (95800320:ℤ)*((117:ℤ)*(packet.w ⬝ᵥ
    (((matrix packet) *ᵥ (1:VI 20))^3 *
      ((matrix packet) *ᵥ ((matrix packet) *ᵥ (1:VI 20))^8)))-D^13)=(-281923)*D^13
  rw [←act_eq packet (1:VI 20),eq_of_eqV node_checked,
    ←act_eq packet (packet.clock^8),←output_eq]
  exact raw_mixed_checked

section Target

variable {R : Type*} [CommRing R]

def targetA (u : R) : Matrix (Fin 20) (Fin 20) R :=
  normalizedA packet u

def targetB (u : R) : Fin 20→R := normalizedB packet u

theorem target_order12 (u : R) (hu : (D:R)*u=1) :
    HasOrder 12 (targetA u) (targetB u) := transport receipts u u hu hu

private theorem cast_defect_zero (u : R) (hu : (D:R)*u=1) (t : FiniteRootedTree)
    (ht : (t.order:Nat)-1=12)
    (paid : (t.factorial:R)*(targetB u ⬝ᵥ Φ t (targetA u))=1) :
    (Int.castRingHom R) (integerDefect t)=0 := by
  let f := Int.castRingHom R
  have hA : (matrix packet).map f = f D • targetA u := by
    change _ = f D • (u • (matrix packet).map f)
    rw [smul_smul,show f D*u=1 from hu,one_smul]
  have hb : f ∘ packet.w = f D • targetB u := by
    change _ = f D • (u • (f∘packet.w))
    rw [smul_smul,show f D*u=1 from hu,one_smul]
  change f ((t.factorial:ℤ)*(packet.w ⬝ᵥ Φ t (matrix packet))-D^13)=0
  simp only [map_sub,map_mul,map_natCast,map_pow,RingHom.map_dotProduct,map_Φ]
  change (t.factorial:R)*((f ∘ packet.w) ⬝ᵥ Φ t ((matrix packet).map f))-(f D)^13=0
  rw [hA,hb,Φ_matrix_smul,ht,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    _ = (f D)^13*((t.factorial:R)*(targetB u ⬝ᵥ Φ t (targetA u))-1) := by ring
    _ = 0 := by rw [paid,sub_self,mul_zero]

theorem target_not_order13 [Nontrivial R] (u : R) (hu : (D:R)*u=1) :
    ¬ HasOrder 13 (targetA u) (targetB u) := by
  intro h
  let f := Int.castRingHom R
  have hB : f (integerDefect bush13)=0 :=
    cast_defect_zero u hu bush13 (by decide +kernel) (h bush13 (by decide +kernel))
  have hM : f (integerDefect mixed13)=0 :=
    cast_defect_zero u hu mixed13 (by decide +kernel) (h mixed13 (by decide +kernel))
  have b0 := congrArg f integer_bush_scaled
  have m0 := congrArg f integer_mixed_scaled
  simp only [map_mul,map_pow,hB,mul_zero] at b0
  simp only [map_mul,map_pow,hM,mul_zero] at m0
  have hD : IsUnit (f D) := IsUnit.of_mul_eq_one _ hu
  obtain ⟨v,hv⟩ := (hD.pow 13).exists_right_inv
  have clear (z : R) (he : 0=z*(f D)^13) : z=0 := by
    have q := congrArg (fun s : R => s*v) he
    change (0:R)*v=(z*(f D)^13)*v at q
    rw [zero_mul,mul_assoc,hv,mul_one] at q
    exact q.symm
  have bb : f 97351=0 := clear _ b0
  have mm : f (-281923)=0 := clear _ m0
  have e := congrArg f two_prime_products
  rw [map_add,map_mul,map_mul,map_one,bb,mm,mul_zero,mul_zero,zero_add] at e
  exact zero_ne_one e

theorem first_diag (u : R) : targetA u 0 0=0 := by
  change u*(matrix packet 0 0:R)=0
  rw [show matrix packet 0 0=0 by decide +kernel,Int.cast_zero,mul_zero]

theorem second_diag (u : R) (hu : (D:R)*u=1) : (16:R)*targetA u 1 1=1 := by
  have e := congrArg (Int.castRingHom R)
    (show (16:ℤ)*matrix packet 1 1=D by decide +kernel)
  simp only [map_mul,Int.coe_castRingHom,Int.cast_ofNat] at e
  change (16:R)*(u*(matrix packet 1 1:R))=1
  calc
    _ = ((16:R)*(matrix packet 1 1:R))*u := by ring
    _ = _ := by rw [e]; exact hu

/-- One genuine lower triangular width-20 tableau over every admissible
nonzero commutative coefficient ring, with exact rooted order twelve. -/
theorem exists_exact_factorial [Nontrivial R] (h : IsUnit (Nat.factorial 12:R)) :
    ∃ (U : Matrix (Fin 20) (Fin 20) R) (w : Fin 20→R),
      U.IsLowerTriangular ∧ U 0 0=0 ∧ (16:R)*U 1 1=1 ∧
      HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  have he : IsUnit (D.toNat:R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) D_paid)
      (by simpa only [Nat.cast_pow] using h.pow 6)
  have hD : IsUnit (D:R) := by
    rw [←D_cast]
    change IsUnit (((D.toNat:ℤ):R))
    simpa only [Int.cast_natCast] using he
  obtain ⟨u,hu⟩ := hD.exists_right_inv
  exact ⟨targetA u,targetB u,normalized_lower packet u,first_diag u,second_diag u hu,
    target_order12 u hu,target_not_order13 u hu⟩

end Target
end RKResearch.Certified.DIRK12FactorialTwentyFlag

#print axioms RKResearch.Certified.DIRK12FactorialTwentyFlag.rational_order12
#print axioms RKResearch.Certified.DIRK12FactorialTwentyFlag.target_not_order13
#print axioms RKResearch.Certified.DIRK12FactorialTwentyFlag.exists_exact_factorial
