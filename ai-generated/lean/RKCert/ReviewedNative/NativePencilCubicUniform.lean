module

public import RKCert.ReviewedNative.NativePencilCubicInteger
public import RKCert.ReviewedNative.NativePencilCubic1009
public import RKCert.ReviewedNative.NativePencilHornerModels
public import RKCert.ReviewedNative.NativePencilResidueBridge
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! # Uniform characteristic-zero cubic port, with no scalar hypotheses beyond the two actual port equations and the nonzero ratio -/
namespace RKResearch.Certified.Graded.NativePencilCubicUniform
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

private abbrev rr := packZ NativePencilCubicInteger.ratioCode
private abbrev aa := packT NativePencilCubicInteger.firstCode
private abbrev hh := packX NativePencilCubicInteger.obstructionCode
private abbrev pp := packX NativePencilCubicInteger.profileCode
private def vR : List (ZMod 1009) := [148,677,986,337,896,722,777,413,80,941,522,890,410,288,946,18,838,639,774,470,128,511,951,240,7,494,972,655,962,783,312,794,822,469,28,413,850,767,62,428,380,288,717,1004,295,301,988,363,974,791,1]
private theorem reducedR : redZ 1009 NativePencilCubicInteger.ratioCode = NativePencilCubic1009.r := by
  have eq : redZ 1009 NativePencilCubicInteger.ratioCode = vR := by decide
  exact eq.trans (show vR = NativePencilCubic1009.r from rfl)
private def vA : List (List (ZMod 1009)) := [[12,977,3,213,550,360,909],[0,769,640,785,99,872,991],[0,0,431,171,415,822,108],[0,0,0,1003,886,972,739],[0,0,0,688,832,296,297],[0,0,0,532,444,733,667]]
private theorem reducedA : redT 1009 NativePencilCubicInteger.firstCode = NativePencilCubic1009.a := by
  have eq : redT 1009 NativePencilCubicInteger.firstCode = vA := by decide
  exact eq.trans (show vA = NativePencilCubic1009.a from rfl)
private def vAL : List (ZMod 1009) := [0,0,0,532,444,733,667]
private theorem reducedAL : redZ 1009 (NativePencilCubicInteger.firstCode.getD 5 []) = NativePencilCubic1009.aLC := by
  have eq : redZ 1009 (NativePencilCubicInteger.firstCode.getD 5 []) = vAL := by decide
  exact eq.trans (show vAL = NativePencilCubic1009.aLC from rfl)
private def vH : List (List (List (ZMod 1009))) := [[[],[981],[420],[927],[584],[425],[707]],[[],[28],[],[5],[303],[587],[921],[995]],[[],[],[589],[1004],[],[125],[92],[495],[84]],[[],[],[],[82],[706],[884],[],[183],[918],[799]],[[],[],[],[],[425],[422],[917],[826],[],[403],[231]],[[],[],[],[],[],[584],[88],[514],[91],[606],[],[513]],[[],[],[],[],[],[],[302],[14],[925],[210],[778],[496]]]
private theorem reducedH : redX 1009 NativePencilCubicInteger.obstructionCode = NativePencilCubic1009.h := by
  have eq : redX 1009 NativePencilCubicInteger.obstructionCode = vH := by decide
  exact eq.trans (show vH = NativePencilCubic1009.h from rfl)
private def vP : List (List (List (ZMod 1009))) := [[[0,12,994]],[[991,985,60]],[[60,969,959]],[[964,60]]]
private theorem reducedP : redX 1009 NativePencilCubicInteger.profileCode = NativePencilCubic1009.p := by
  have eq : redX 1009 NativePencilCubicInteger.profileCode = vP := by decide
  exact eq.trans (show vP = NativePencilCubic1009.p from rfl)
private def vPL : List (List (ZMod 1009)) := [[964,60]]
private theorem reducedPL : redT 1009 (NativePencilCubicInteger.profileCode.getD 3 []) = [NativePencilCubic1009.pLC] := by
  have eq : redT 1009 (NativePencilCubicInteger.profileCode.getD 3 []) = vPL := by decide
  exact eq.trans (show vPL = [NativePencilCubic1009.pLC] from rfl)

private theorem ratio_len : NativePencilCubicInteger.ratioCode.length ≤ 50+1 := by decide

private theorem ratio_int_top :
    NativePencilCubicInteger.ratioCode.getD 50 0 ≠ (0 : ℤ) := by decide

private theorem ratio_mod_top :
    Int.castRingHom (ZMod 1009) (NativePencilCubicInteger.ratioCode.getD 50 0) = 1 := by decide

private theorem rr_degree : rr.natDegree = 50 := by
  have bound : rr.natDegree ≤ 50 := pack_bound NativePencilCubicInteger.ratioCode 50 ratio_len
  have top : rr.coeff 50 ≠ 0 := by
    rw [pack_coeff]
    exact ratio_int_top
  exact natDegree_eq_of_le_of_coeff_ne_zero bound top

private theorem rr_good : intResidue rr.leadingCoeff ≠ 0 := by
  rw [← coeff_natDegree,rr_degree,pack_coeff,int_via_residue,ratio_mod_top,map_one]
  exact one_ne_zero

private theorem a_bound : aa.natDegree ≤ 5 := by
  apply pack_bound (NativePencilCubicInteger.firstCode.map packZ) 5
  rw [List.length_map]
  decide

private theorem r_eval (z : k) : zEval z rr = NativePencilCubic1009.ratioForm q z := by
  rw [eval_packZ,foldZ_reduce q,reducedR] <;> rfl
private theorem a_eval (z t : k) : tEval z t aa = NativePencilCubic1009.firstPort q z t := by
  rw [eval_packT,foldT_reduce q,reducedA] <;> rfl
private theorem a_lead (z : k) : zEval z (aa.coeff 5) = NativePencilCubic1009.firstPortLeading q z := by
  rw [coeff_packT,eval_packZ,foldZ_reduce q,reducedAL] <;> rfl

private theorem p_bound : pp.natDegree ≤ 3 := by
  apply pack_bound (NativePencilCubicInteger.profileCode.map packT) 3
  rw [List.length_map]
  decide

private theorem p_lead (z t : k) : tEval z t (pp.coeff 3) = NativePencilCubic1009.profileLeading q z := by
  rw [coeff_packX,eval_packT,foldT_reduce q,reducedPL]
  change NativePencilCubic1009.vz q z NativePencilCubic1009.pLC + t*0 = NativePencilCubic1009.vz q z NativePencilCubic1009.pLC
  rw [mul_zero,add_zero]

private theorem h_eval (z t x : k) : hh.eval₂ (tEval z t) x = NativePencilCubic1009.obstructedForm q z t x := by
  rw [eval_packX,foldX_reduce q,reducedH] <;> rfl
private theorem p_eval (z t x : k) : pp.eval₂ (tEval z t) x = NativePencilCubic1009.profileForm q z t x := by
  rw [eval_packX,foldX_reduce q,reducedP] <;> rfl

private theorem residue_gate (Z : k) (hr : zEval Z rr = 0) :
    zEval Z (aa.coeff 5) ≠ 0 ∧
      ∀ T : k, tEval Z T aa = 0 → tEval Z T (pp.coeff 3) ≠ 0 ∧
        ∀ x : k, pp.eval₂ (tEval Z T) x = 0 → hh.eval₂ (tEval Z T) x ≠ 0 := by
  have ratio : NativePencilCubic1009.ratioForm q Z = 0 := (r_eval Z).symm.trans hr
  refine ⟨?_,?_⟩
  · rw [a_lead]
    exact NativePencilCubic1009.firstPortLeading_ne_zero q Z ratio
  · intro T ht
    have first : NativePencilCubic1009.firstPort q Z T = 0 := (a_eval Z T).symm.trans ht
    refine ⟨?_,?_⟩
    · rw [p_lead]
      exact NativePencilCubic1009.profileLeading_ne_zero q Z ratio
    · intro x hx
      have root : NativePencilCubic1009.profileForm q Z T x = 0 := (p_eval Z T x).symm.trans hx
      rw [h_eval]
      exact NativePencilCubic1009.obstructedForm_ne_zero q Z T x ratio first root

private abbrev inner : TPoly := hh.resultant pp hh.natDegree 3

private theorem residue_coprime :
    IsCoprime (rr.map intResidue) ((aa.resultant inner 5 inner.natDegree).map intResidue) :=
  residue_nested_projection_coprime (k:=k) rr aa hh pp 5 3 a_bound p_bound residue_gate

/-- Actual degree-six pencil obstruction and cubic profile are coprime after
all characteristic-zero parameter specializations satisfying the first ports. -/
theorem scalar_coprime {K : Type*} [Field K] [CharZero K] (z t : K) (zn : z≠0)
    (az : NativePencilCubicInteger.firstPort z t=0) (cz : NativePencilCubicInteger.secondPort z t=0) :
    IsCoprime ((packX NativePencilCubicInteger.obstructionCode).map (tEval z t))
      ((packX NativePencilCubicInteger.profileCode).map (tEval z t)) := by
  have rz : zEval z rr=0 := by
    rw [eval_packZ]
    exact NativePencilCubicInteger.ratioForm_eq_zero z t zn az cz
  have a0 : tEval z t aa=0 := by rw [eval_packT]; exact az
  have innerSize : hh.natDegree ≠ 0 ∨ (3:ℕ) ≠ 0 := Or.inr (by decide)
  have outerSize : (5:ℕ) ≠ 0 ∨ inner.natDegree ≠ 0 := Or.inl (by decide)
  have outerBound : (hh.resultant pp hh.natDegree 3).natDegree ≤ inner.natDegree := le_rfl
  exact projected_coprime intResidue rr rr_good aa hh pp hh.natDegree 3 le_rfl p_bound
    innerSize 5 inner.natDegree a_bound outerBound outerSize residue_coprime z t rz a0

end
end RKResearch.Certified.Graded.NativePencilCubicUniform
