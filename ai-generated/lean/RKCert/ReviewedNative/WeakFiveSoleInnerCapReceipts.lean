module

public import RKCert.ReviewedNative.WeakFiveSoleInnerCapAlgebra
public import RKCert.ReviewedNative.WeakFiveSoleInnerIntegerCornerData

import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-cleared four-axis cap receipts, 480 vertices total

All rational endpoints come from the frozen 30 corner cages. No
additional root computation or rational solve is used. The integer
certificate uses only 30 independent sixteen-vertex proof boundaries. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

structure FracCode where
  num : ℤ
  den : ℤ

def betaLowerNum (cell : Fin 15) (j : Fin 6) : ℕ := (highCellCorner cell).lower j
def betaUpperNum (cell : Fin 15) (j : Fin 6) : ℕ := (lowCellCorner cell).lower j + 1

def gammaCode (d : CornerRow) (z : ℕ) : FracCode :=
  ⟨(d.ratioDen : ℤ)*(d.remaining : ℤ)*(4096-(z : ℤ)), (d.rightDen : ℤ)*4096⟩

def shiftCode (z x : ℕ) : FracCode := ⟨(z : ℤ)-(x : ℤ),4096-(z : ℤ)⟩

def gammaLoCode (p : Phase) (cell : Fin 15) : FracCode :=
  gammaCode (highCellCorner cell) (betaUpperNum cell p.zIndex)

def gammaHiCode (p : Phase) (cell : Fin 15) : FracCode :=
  gammaCode (lowCellCorner cell) (betaLowerNum cell p.zIndex)

def shiftLoCode (p : Phase) (cell : Fin 15) (j : Fin 3) : FracCode :=
  shiftCode (betaLowerNum cell p.zIndex) (betaUpperNum cell (p.rootIndex j))

def shiftHiCode (p : Phase) (cell : Fin 15) (j : Fin 3) : FracCode :=
  shiftCode (betaUpperNum cell p.zIndex) (betaLowerNum cell (p.rootIndex j))

def capMillion : Phase → ℤ
  | .A => -514
  | .B => -38

def mixedNumerator (p : Phase) (j : Fin 4) (g : FracCode) : ℤ :=
  g.den*p.scaledBase j.castSucc + g.num*(p.scaledBase j.succ-p.scaledBase j.castSucc)

def testClear (g a b c : FracCode) : ℤ := 420*g.den*a.den*b.den*c.den

def testNumerator (p : Phase) (g a b c : FracCode) : ℤ :=
  mixedNumerator p 3 g*(a.den*b.den*c.den) +
  mixedNumerator p 2 g*(a.num*b.den*c.den+a.den*b.num*c.den+a.den*b.den*c.num) +
  mixedNumerator p 1 g*(a.num*b.num*c.den+a.num*b.den*c.num+a.den*b.num*c.num) +
  mixedNumerator p 0 g*(a.num*b.num*c.num)

def vertexOK (p : Phase) (g a b c : FracCode) : Prop :=
  0 < g.den ∧ 0 < a.den ∧ 0 < b.den ∧ 0 < c.den ∧
    1000000*testNumerator p g a b c ≤ capMillion p*testClear g a b c

def checkedVertex (p : Phase) (j : Fin 15) (g a b c : Bool) : Prop :=
  vertexOK p (pick (gammaLoCode p j) (gammaHiCode p j) g)
    (pick (shiftLoCode p j 0) (shiftHiCode p j 0) a)
    (pick (shiftLoCode p j 1) (shiftHiCode p j 1) b)
    (pick (shiftLoCode p j 2) (shiftHiCode p j 2) c)

set_option maxRecDepth 2800
set_option maxHeartbeats 960000

private theorem capA00 (a b c d : Bool) : checkedVertex .A 0 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA01 (a b c d : Bool) : checkedVertex .A 1 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA02 (a b c d : Bool) : checkedVertex .A 2 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA03 (a b c d : Bool) : checkedVertex .A 3 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA04 (a b c d : Bool) : checkedVertex .A 4 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA05 (a b c d : Bool) : checkedVertex .A 5 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA06 (a b c d : Bool) : checkedVertex .A 6 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA07 (a b c d : Bool) : checkedVertex .A 7 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA08 (a b c d : Bool) : checkedVertex .A 8 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA09 (a b c d : Bool) : checkedVertex .A 9 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA10 (a b c d : Bool) : checkedVertex .A 10 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA11 (a b c d : Bool) : checkedVertex .A 11 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA12 (a b c d : Bool) : checkedVertex .A 12 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA13 (a b c d : Bool) : checkedVertex .A 13 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capA14 (a b c d : Bool) : checkedVertex .A 14 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB00 (a b c d : Bool) : checkedVertex .B 0 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB01 (a b c d : Bool) : checkedVertex .B 1 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB02 (a b c d : Bool) : checkedVertex .B 2 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB03 (a b c d : Bool) : checkedVertex .B 3 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB04 (a b c d : Bool) : checkedVertex .B 4 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB05 (a b c d : Bool) : checkedVertex .B 5 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB06 (a b c d : Bool) : checkedVertex .B 6 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB07 (a b c d : Bool) : checkedVertex .B 7 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB08 (a b c d : Bool) : checkedVertex .B 8 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB09 (a b c d : Bool) : checkedVertex .B 9 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB10 (a b c d : Bool) : checkedVertex .B 10 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB11 (a b c d : Bool) : checkedVertex .B 11 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB12 (a b c d : Bool) : checkedVertex .B 12 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB13 (a b c d : Bool) : checkedVertex .B 13 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem capB14 (a b c d : Bool) : checkedVertex .B 14 a b c d := by
  unfold checkedVertex vertexOK
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

/-- All 480 corners with strictly positive cleared denominators. -/
theorem all_checked_vertices (p : Phase) (j : Fin 15) (g a b c : Bool) :
    checkedVertex p j g a b c := by
  cases p
  · fin_cases j
    · exact capA00 g a b c
    · exact capA01 g a b c
    · exact capA02 g a b c
    · exact capA03 g a b c
    · exact capA04 g a b c
    · exact capA05 g a b c
    · exact capA06 g a b c
    · exact capA07 g a b c
    · exact capA08 g a b c
    · exact capA09 g a b c
    · exact capA10 g a b c
    · exact capA11 g a b c
    · exact capA12 g a b c
    · exact capA13 g a b c
    · exact capA14 g a b c
  · fin_cases j
    · exact capB00 g a b c
    · exact capB01 g a b c
    · exact capB02 g a b c
    · exact capB03 g a b c
    · exact capB04 g a b c
    · exact capB05 g a b c
    · exact capB06 g a b c
    · exact capB07 g a b c
    · exact capB08 g a b c
    · exact capB09 g a b c
    · exact capB10 g a b c
    · exact capB11 g a b c
    · exact capB12 g a b c
    · exact capB13 g a b c
    · exact capB14 g a b c

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def FracCode.value (d : FracCode) (K : Type*) [Field K] : K := (d.num : K)/(d.den : K)

theorem capMillion_neg (p : Phase) : (capMillion p : K) < 0 := by
  cases p <;> norm_num [capMillion]

private theorem cleared_field_value (p : Phase) (g a b c : FracCode)
    (hg : (g.den : K) ≠ 0) (ha : (a.den : K) ≠ 0) (hb : (b.den : K) ≠ 0)
    (hc : (c.den : K) ≠ 0) :
    (testNumerator p g a b c : K) =
      (testClear g a b c : K)*signedTest p (g.value K) (a.value K) (b.value K) (c.value K) := by
  simp only [testNumerator,mixedNumerator,testClear,signedTest,Phase.mixedPower,FracCode.value,
    Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
  field_simp [hg,ha,hb,hc] <;> ring

theorem vertex_bound {p : Phase} {g a b c : FracCode} (pass : vertexOK p g a b c) :
    signedTest p (g.value K) (a.value K) (b.value K) (c.value K) ≤ (capMillion p : K)/1000000 := by
  obtain ⟨pg,pa,pb,pc,pay⟩ := pass
  have pg' : (0 : K) < (g.den : K) := Int.cast_pos.mpr pg
  have pa' : (0 : K) < (a.den : K) := Int.cast_pos.mpr pa
  have pb' : (0 : K) < (b.den : K) := Int.cast_pos.mpr pb
  have pc' : (0 : K) < (c.den : K) := Int.cast_pos.mpr pc
  have hd : (0 : K) < (testClear g a b c : K) := by
    simp only [testClear,Int.cast_mul,Int.cast_ofNat]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) pg') pa') pb') pc'
  have paid : (1000000 : K)*(testNumerator p g a b c : K) ≤
      (capMillion p : K)*(testClear g a b c : K) := by exact_mod_cast pay
  rw [cleared_field_value p g a b c pg'.ne' pa'.ne' pb'.ne' pc'.ne'] at paid
  apply (le_div_iff₀ (by norm_num : (0 : K) < 1000000)).mpr
  apply le_of_mul_le_mul_right _ hd
  simpa only [mul_comm,mul_left_comm,mul_assoc] using paid

private theorem FracCode.pick_value (l h : FracCode) (b : Bool) :
    (pick l h b).value K = pick (l.value K) (h.value K) b := by cases b <;> rfl

/-- Reusable four-axis box consumer for any actual root/coordinate
producer that supplies the literal cage inequalities. -/
theorem cap_of_code_box (p : Phase) (cell : Fin 15) {g a b c : K}
    (gb : (gammaLoCode p cell).value K≤g ∧ g≤(gammaHiCode p cell).value K)
    (ab : (shiftLoCode p cell 0).value K≤a ∧ a≤(shiftHiCode p cell 0).value K)
    (bb : (shiftLoCode p cell 1).value K≤b ∧ b≤(shiftHiCode p cell 1).value K)
    (cb : (shiftLoCode p cell 2).value K≤c ∧ c≤(shiftHiCode p cell 2).value K) :
    signedTest p g a b c ≤ (capMillion p : K)/1000000 := by
  apply signedTest_le_of_vertices p gb ab bb cb
  intro i j k l
  simpa only [FracCode.pick_value] using (vertex_bound (K := K) (all_checked_vertices p cell i j k l))

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
