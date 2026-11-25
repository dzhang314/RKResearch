module

public import RKCert.ReviewedNative.NativePencilQuarticInteger
public import RKCert.ReviewedNative.NativePencilQuartic1009
public import RKCert.ReviewedNative.NativePencilHornerModels
public import RKCert.ReviewedNative.NativePencilResidueBridge
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! # Uniform characteristic-zero quartic port, with no scalar hypotheses beyond the two actual port equations -/
namespace RKResearch.Certified.Graded.NativePencilQuarticUniform
open Polynomial NativeHornerWitness NativePencilProjection
noncomputable section
set_option maxRecDepth 8192 in
private theorem prime1009 : Nat.Prime 1009 := by decide

local instance : Fact (Nat.Prime 1009) := ⟨prime1009⟩
private abbrev k := AlgebraicClosure (ZMod 1009)
private abbrev q : ZMod 1009 →+* k := algebraMap (ZMod 1009) k
private abbrev intResidue : ℤ →+* k := Int.castRingHom k

private theorem int_via_residue (a : ℤ) :
    intResidue a = q (Int.castRingHom (ZMod 1009) a) := (map_intCast q a).symm

private abbrev rr := packZ NativePencilQuarticInteger.ratioCode
private abbrev aa := packT NativePencilQuarticInteger.firstCode
private abbrev bb := packT (NativePencilQuarticInteger.obstructionCode.getD 0 [])
private def vR : List (ZMod 1009) := [277,806,402,133,661,384,886,290,391,124,808,520,61,372,853,59,835,217,572,842,806,946,879,735,629,480,177,869,355,308,897,676,898,929,877,738,451,430,727,203,1]
private theorem reducedR : redZ 1009 NativePencilQuarticInteger.ratioCode = NativePencilQuartic1009.r := by
  have eq : redZ 1009 NativePencilQuarticInteger.ratioCode = vR := by decide
  exact eq.trans (show vR = NativePencilQuartic1009.r from rfl)
private def vA : List (List (ZMod 1009)) := [[592],[407,67],[551,364,458],[930,723,410,551],[956,97,567,73,862],[4,879,526,841,922],[836,226,693,809,522],[358,541,788,978,713],[750,737,918,879,931],[414,295,621,828,233]]
private theorem reducedA : redT 1009 NativePencilQuarticInteger.firstCode = NativePencilQuartic1009.a := by
  have eq : redT 1009 NativePencilQuarticInteger.firstCode = vA := by decide
  exact eq.trans (show vA = NativePencilQuartic1009.a from rfl)
private def vAL : List (ZMod 1009) := [414,295,621,828,233]
private theorem reducedAL : redZ 1009 (NativePencilQuarticInteger.firstCode.getD 9 []) = NativePencilQuartic1009.aLC := by
  have eq : redZ 1009 (NativePencilQuarticInteger.firstCode.getD 9 []) = vAL := by decide
  exact eq.trans (show vAL = NativePencilQuartic1009.aLC from rfl)
private def vB : List (List (ZMod 1009)) := [[278,417,731],[790,828,757,919],[1004,912,398,764,583],[475,939,949,495,502,946],[53,288,466,234,705,195,385],[936,653,53,92,680,138,744],[674,461,836,170,563,384,57],[423,197,961,618,632,311,153,674],[769,666,178,119,197,998,608,611,108],[510,173,431,417,562,258,541,496,270,181],[0,514,734,370,772,814,824,842,908,416],[0,0,474,880,78,825,850,289,898,531],[0,0,0,468,464,656,988,728,826,186],[0,0,0,0,210,807,619,317,295,199],[0,0,0,0,0,78,570,598,243,324]]
private theorem reducedB : redT 1009 (NativePencilQuarticInteger.obstructionCode.getD 0 []) = vB := by decide

private theorem ratio_len : NativePencilQuarticInteger.ratioCode.length ≤ 40+1 := by decide

private theorem ratio_int_top :
    NativePencilQuarticInteger.ratioCode.getD 40 0 ≠ (0 : ℤ) := by decide

private theorem ratio_mod_top :
    Int.castRingHom (ZMod 1009) (NativePencilQuarticInteger.ratioCode.getD 40 0) = 1 := by decide

private theorem rr_degree : rr.natDegree = 40 := by
  have bound : rr.natDegree ≤ 40 := pack_bound NativePencilQuarticInteger.ratioCode 40 ratio_len
  have top : rr.coeff 40 ≠ 0 := by
    rw [pack_coeff]
    exact ratio_int_top
  exact natDegree_eq_of_le_of_coeff_ne_zero bound top

private theorem rr_good : intResidue rr.leadingCoeff ≠ 0 := by
  rw [← coeff_natDegree,rr_degree,pack_coeff,int_via_residue,ratio_mod_top,map_one]
  exact one_ne_zero

private theorem a_bound : aa.natDegree ≤ 9 := by
  apply pack_bound (NativePencilQuarticInteger.firstCode.map packZ) 9
  rw [List.length_map]
  decide

private theorem r_eval (z : k) : zEval z rr = NativePencilQuartic1009.ratioForm q z := by
  rw [eval_packZ,foldZ_reduce q,reducedR] <;> rfl
private theorem a_eval (z t : k) : tEval z t aa = NativePencilQuartic1009.firstPort q z t := by
  rw [eval_packT,foldT_reduce q,reducedA] <;> rfl
private theorem a_lead (z : k) : zEval z (aa.coeff 9) = NativePencilQuartic1009.firstPortLeading q z := by
  rw [coeff_packT,eval_packZ,foldZ_reduce q,reducedAL] <;> rfl

private theorem witness_obstruction_shape : NativePencilQuartic1009.h = [vB] := rfl

private theorem witness_eval_at_zero (z t : k) (b : List (List (ZMod 1009))) :
    NativePencilQuartic1009.vx q z t 0 [b] = NativePencilQuartic1009.vt q z t b := by
  change NativePencilQuartic1009.vt q z t b + (0:k)*0 = _
  rw [zero_mul,add_zero]

private theorem b_eval (z t : k) : tEval z t bb = NativePencilQuartic1009.obstructedForm q z t 0 := by
  calc
    _ = NativePencilQuartic1009.vt q z t vB := by rw [eval_packT,foldT_reduce q,reducedB]
    _ = NativePencilQuartic1009.vx q z t 0 [vB] := (witness_eval_at_zero z t vB).symm
    _ = _ := by rw [NativePencilQuartic1009.obstructedForm,witness_obstruction_shape]

private theorem residue_gate (Z : k) (hr : zEval Z rr = 0) :
    zEval Z (aa.coeff 9) ≠ 0 ∧
      ∀ T : k, tEval Z T aa = 0 → tEval Z T bb ≠ 0 := by
  have ratio : NativePencilQuartic1009.ratioForm q Z = 0 := (r_eval Z).symm.trans hr
  refine ⟨?_,?_⟩
  · rw [a_lead]
    exact NativePencilQuartic1009.firstPortLeading_ne_zero q Z ratio
  · intro T ht
    have first : NativePencilQuartic1009.firstPort q Z T = 0 := (a_eval Z T).symm.trans ht
    rw [b_eval]
    exact NativePencilQuartic1009.obstructedForm_ne_zero q Z T 0 ratio first

private theorem residue_coprime :
    IsCoprime (rr.map intResidue) ((aa.resultant bb 9 bb.natDegree).map intResidue) :=
  residue_projection_coprime (k:=k) rr aa bb 9 bb.natDegree a_bound le_rfl residue_gate

/-- The integer-normalized third primitive cannot vanish anywhere on the
actual first two quartic port equations over a characteristic-zero field. -/
theorem scalar_ne_zero {K : Type*} [Field K] [CharZero K] (z t : K)
    (az : NativePencilQuarticInteger.firstPort z t=0) (mz : NativePencilQuarticInteger.secondPort z t=0) :
    foldT z t (NativePencilQuarticInteger.obstructionCode.getD 0 []) ≠ 0 := by
  have rz : zEval z rr=0 := by
    rw [eval_packZ]
    exact NativePencilQuarticInteger.ratioForm_eq_zero z t az mz
  have a0 : tEval z t aa=0 := by rw [eval_packT]; exact az
  have size : (9:ℕ) ≠ 0 ∨ bb.natDegree ≠ 0 := Or.inl (by decide)
  have hn : tEval z t bb ≠ 0 :=
    projected_value_ne_zero intResidue rr rr_good aa bb 9 bb.natDegree
      a_bound le_rfl size residue_coprime z t rz a0
  rw [eval_packT] at hn
  exact hn

end
end RKResearch.Certified.Graded.NativePencilQuarticUniform
