module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Fifteen rational stages of exact strict SDIRK order eight

The integer-scaled reviewed tree replay is split by actual finite
lists and their full remainders. Only the next tall tree is needed
for exactness. This is an upper construction, not a minimum. -/

namespace RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper

open FiniteRootedTree
open scoped Matrix

/-- The chronological stage numerator matrix 1540104384000 A. -/
def AInt : Matrix (Fin 15) (Fin 15) ℤ :=
  !![192513048000,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
     385026096000,192513048000,0,0,0,0,0,0,0,0,0,0,0,0,0;
     216577179000,-24064131000,192513048000,0,0,0,0,0,0,0,0,0,0,0,0;
     -517378816500,-156416851500,481282620000,192513048000,0,0,0,0,0,0,0,0,0,0,0;
     1732617432000,577539144000,-1347591336000,-385026096000,192513048000,0,0,0,0,0,0,0,0,0,0;
     1780745694000,914436978000,-1540104384000,-385026096000,0,192513048000,0,0,0,0,0,0,0,0,0;
     888521760000,928011616000,-1224185536000,-78979712000,-380089864000,59234784000,192513048000,0,0,0,0,0,0,0,0;
     444260880000,592347840000,-740434800000,-296173920000,-222130440000,29617392000,0,192513048000,0,0,0,0,0,0,0;
     -403536966000,-481899649000,616411971000,156725366000,185725729000,-25298189000,-48128262000,0,192513048000,0,0,0,0,0,0;
     -7641287136000,-8648278464000,11195374176000,2013982656000,3243104424000,-355408704000,1155078288000,0,0,192513048000,0,0,0,0,0;
     -17326174320000,-19507988864000,25283380304000,4363629088000,5839562456000,385026096000,2310156576000,0,0,0,192513048000,0,0,0,0;
     -9050427114750,-10214298066000,13231107104250,2327741902500,3658904841375,-280902452250,156416851500,-219585195375,957064867200,-233422070700,52425428250,192513048000,0,0,0;
     37885975498560,42957855153920,-55586513653440,-10143759310720,-14918181625760,817242569920,-929196311680,1383527104960,-1675633569792,992853959552,-206630671520,0,192513048000,0,0;
     -23505925999500,-26630736419000,34466045085500,6249620839000,8869610345750,-202479259500,1130216451000,-662860448250,1234028390400,-749497967400,132096315000,370135584000,69799275000,192513048000,0;
     11411353647750,12880489244000,-16684273793250,-2938271192500,-4129336239875,-33385766750,-1072665639500,190859771375,308653363200,310598588300,-72311807750,346813376000,302654625000,333900112000,192513048000]

/-- The output numerator row 33075 b. -/
def bInt : Fin 15 → ℤ := ![0,0,0,0,0,0,2506,1282,5844,2506,1282,5068,3675,5068,5844]

def A : Matrix (Fin 15) (Fin 15) ℚ := Matrix.of fun i j => (AInt i j : ℚ) / 1540104384000

def b : Fin 15 → ℚ := fun i => (bInt i : ℚ) / 33075

set_option maxHeartbeats 8000000 in
theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 15, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1/8 := by
  intro i
  fin_cases i <;> decide +kernel

theorem cast_AInt :
    AInt.map (Int.castRingHom ℚ) = (1540104384000 : ℚ) • A := by
  funext i j
  change (AInt i j : ℚ) = (1540104384000 : ℚ) * ((AInt i j : ℚ) / 1540104384000)
  exact (mul_div_cancel₀ (AInt i j : ℚ) (by decide +kernel : (1540104384000 : ℚ) ≠ 0)).symm

theorem cast_bInt :
    (Int.castRingHom ℚ) ∘ bInt = (33075 : ℚ) • b := by
  funext i
  change (bInt i : ℚ) = (33075 : ℚ) * ((bInt i : ℚ) / 33075)
  exact (mul_div_cancel₀ (bInt i : ℚ) (by decide +kernel : (33075 : ℚ) ≠ 0)).symm

-- Supply the existing evaluator with only the nonzero matrix terms.
def actInt (v : Fin 15 → ℤ) : Fin 15 → ℤ :=
  ![(192513048000) * v (0 : Fin 15),
    (385026096000) * v (0 : Fin 15) + ((192513048000) * v (1 : Fin 15)),
    (216577179000) * v (0 : Fin 15) + ((-24064131000) * v (1 : Fin 15) + ((192513048000) * v (2 : Fin 15))),
    (-517378816500) * v (0 : Fin 15) + ((-156416851500) * v (1 : Fin 15) + ((481282620000) * v (2 : Fin 15) + ((192513048000) * v (3 : Fin 15)))),
    (1732617432000) * v (0 : Fin 15) + ((577539144000) * v (1 : Fin 15) + ((-1347591336000) * v (2 : Fin 15) + ((-385026096000) * v (3 : Fin 15) + ((192513048000) * v (4 : Fin 15))))),
    (1780745694000) * v (0 : Fin 15) + ((914436978000) * v (1 : Fin 15) + ((-1540104384000) * v (2 : Fin 15) + ((-385026096000) * v (3 : Fin 15) + ((192513048000) * v (5 : Fin 15))))),
    (888521760000) * v (0 : Fin 15) + ((928011616000) * v (1 : Fin 15) + ((-1224185536000) * v (2 : Fin 15) + ((-78979712000) * v (3 : Fin 15) + ((-380089864000) * v (4 : Fin 15) + ((59234784000) * v (5 : Fin 15) + ((192513048000) * v (6 : Fin 15))))))),
    (444260880000) * v (0 : Fin 15) + ((592347840000) * v (1 : Fin 15) + ((-740434800000) * v (2 : Fin 15) + ((-296173920000) * v (3 : Fin 15) + ((-222130440000) * v (4 : Fin 15) + ((29617392000) * v (5 : Fin 15) + ((192513048000) * v (7 : Fin 15))))))),
    (-403536966000) * v (0 : Fin 15) + ((-481899649000) * v (1 : Fin 15) + ((616411971000) * v (2 : Fin 15) + ((156725366000) * v (3 : Fin 15) + ((185725729000) * v (4 : Fin 15) + ((-25298189000) * v (5 : Fin 15) + ((-48128262000) * v (6 : Fin 15) + ((192513048000) * v (8 : Fin 15)))))))),
    (-7641287136000) * v (0 : Fin 15) + ((-8648278464000) * v (1 : Fin 15) + ((11195374176000) * v (2 : Fin 15) + ((2013982656000) * v (3 : Fin 15) + ((3243104424000) * v (4 : Fin 15) + ((-355408704000) * v (5 : Fin 15) + ((1155078288000) * v (6 : Fin 15) + ((192513048000) * v (9 : Fin 15)))))))),
    (-17326174320000) * v (0 : Fin 15) + ((-19507988864000) * v (1 : Fin 15) + ((25283380304000) * v (2 : Fin 15) + ((4363629088000) * v (3 : Fin 15) + ((5839562456000) * v (4 : Fin 15) + ((385026096000) * v (5 : Fin 15) + ((2310156576000) * v (6 : Fin 15) + ((192513048000) * v (10 : Fin 15)))))))),
    (-9050427114750) * v (0 : Fin 15) + ((-10214298066000) * v (1 : Fin 15) + ((13231107104250) * v (2 : Fin 15) + ((2327741902500) * v (3 : Fin 15) + ((3658904841375) * v (4 : Fin 15) + ((-280902452250) * v (5 : Fin 15) + ((156416851500) * v (6 : Fin 15) + ((-219585195375) * v (7 : Fin 15) + ((957064867200) * v (8 : Fin 15) + ((-233422070700) * v (9 : Fin 15) + ((52425428250) * v (10 : Fin 15) + ((192513048000) * v (11 : Fin 15)))))))))))),
    (37885975498560) * v (0 : Fin 15) + ((42957855153920) * v (1 : Fin 15) + ((-55586513653440) * v (2 : Fin 15) + ((-10143759310720) * v (3 : Fin 15) + ((-14918181625760) * v (4 : Fin 15) + ((817242569920) * v (5 : Fin 15) + ((-929196311680) * v (6 : Fin 15) + ((1383527104960) * v (7 : Fin 15) + ((-1675633569792) * v (8 : Fin 15) + ((992853959552) * v (9 : Fin 15) + ((-206630671520) * v (10 : Fin 15) + ((192513048000) * v (12 : Fin 15)))))))))))),
    (-23505925999500) * v (0 : Fin 15) + ((-26630736419000) * v (1 : Fin 15) + ((34466045085500) * v (2 : Fin 15) + ((6249620839000) * v (3 : Fin 15) + ((8869610345750) * v (4 : Fin 15) + ((-202479259500) * v (5 : Fin 15) + ((1130216451000) * v (6 : Fin 15) + ((-662860448250) * v (7 : Fin 15) + ((1234028390400) * v (8 : Fin 15) + ((-749497967400) * v (9 : Fin 15) + ((132096315000) * v (10 : Fin 15) + ((370135584000) * v (11 : Fin 15) + ((69799275000) * v (12 : Fin 15) + ((192513048000) * v (13 : Fin 15)))))))))))))),
    (11411353647750) * v (0 : Fin 15) + ((12880489244000) * v (1 : Fin 15) + ((-16684273793250) * v (2 : Fin 15) + ((-2938271192500) * v (3 : Fin 15) + ((-4129336239875) * v (4 : Fin 15) + ((-33385766750) * v (5 : Fin 15) + ((-1072665639500) * v (6 : Fin 15) + ((190859771375) * v (7 : Fin 15) + ((308653363200) * v (8 : Fin 15) + ((310598588300) * v (9 : Fin 15) + ((-72311807750) * v (10 : Fin 15) + ((346813376000) * v (11 : Fin 15) + ((302654625000) * v (12 : Fin 15) + ((333900112000) * v (13 : Fin 15) + ((192513048000) * v (14 : Fin 15)))))))))))))))]

def outInt (v : Fin 15 → ℤ) : ℤ :=
  (2506) * v (6 : Fin 15) + ((1282) * v (7 : Fin 15) + ((5844) * v (8 : Fin 15) + ((2506) * v (9 : Fin 15) + ((1282) * v (10 : Fin 15) + ((5068) * v (11 : Fin 15) + ((3675) * v (12 : Fin 15) + ((5068) * v (13 : Fin 15) + ((5844) * v (14 : Fin 15)))))))))

-- Kernel-check precisely the Fin 15 indices produced by the native dot-product recursion.

private theorem finSuccToNumeral1 :
    (Fin.succ (0 : Fin 14) : Fin 15) = (1 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral2 :
    (Fin.succ (Fin.succ (0 : Fin 13)) : Fin 15) = (2 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral3 :
    (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12))) : Fin 15) = (3 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral4 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11)))) : Fin 15) = (4 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral5 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10))))) : Fin 15) = (5 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral6 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9)))))) : Fin 15) = (6 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral7 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8))))))) : Fin 15) = (7 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral8 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7)))))))) : Fin 15) = (8 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral9 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6))))))))) : Fin 15) = (9 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral10 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5)))))))))) : Fin 15) = (10 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral11 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4))))))))))) : Fin 15) = (11 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral12 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3)))))))))))) : Fin 15) = (12 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral13 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))))))))))) : Fin 15) = (13 : Fin 15) := by
  decide +kernel

private theorem finSuccToNumeral14 :
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))))))))))) : Fin 15) = (14 : Fin 15) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem actInt_eq (v : Fin 15 → ℤ) : actInt v = AInt *ᵥ v := by
  funext i
  fin_cases i
  · change (192513048000) * v (0 : Fin 15) =
      (![ 192513048000,0,0,0,0,0,0,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero]
  · change (385026096000) * v (0 : Fin 15) + ((192513048000) * v (1 : Fin 15)) =
      (![ 385026096000,192513048000,0,0,0,0,0,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1]
  · change (216577179000) * v (0 : Fin 15) + ((-24064131000) * v (1 : Fin 15) + ((192513048000) * v (2 : Fin 15))) =
      (![ 216577179000,-24064131000,192513048000,0,0,0,0,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2]
  · change (-517378816500) * v (0 : Fin 15) + ((-156416851500) * v (1 : Fin 15) + ((481282620000) * v (2 : Fin 15) + ((192513048000) * v (3 : Fin 15)))) =
      (![ -517378816500,-156416851500,481282620000,192513048000,0,0,0,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3]
  · change (1732617432000) * v (0 : Fin 15) + ((577539144000) * v (1 : Fin 15) + ((-1347591336000) * v (2 : Fin 15) + ((-385026096000) * v (3 : Fin 15) + ((192513048000) * v (4 : Fin 15))))) =
      (![ 1732617432000,577539144000,-1347591336000,-385026096000,192513048000,0,0,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4]
  · change (1780745694000) * v (0 : Fin 15) + ((914436978000) * v (1 : Fin 15) + ((-1540104384000) * v (2 : Fin 15) + ((-385026096000) * v (3 : Fin 15) + ((192513048000) * v (5 : Fin 15))))) =
      (![ 1780745694000,914436978000,-1540104384000,-385026096000,0,192513048000,0,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral5]
  · change (888521760000) * v (0 : Fin 15) + ((928011616000) * v (1 : Fin 15) + ((-1224185536000) * v (2 : Fin 15) + ((-78979712000) * v (3 : Fin 15) + ((-380089864000) * v (4 : Fin 15) + ((59234784000) * v (5 : Fin 15) + ((192513048000) * v (6 : Fin 15))))))) =
      (![ 888521760000,928011616000,-1224185536000,-78979712000,-380089864000,59234784000,192513048000,0,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6]
  · change (444260880000) * v (0 : Fin 15) + ((592347840000) * v (1 : Fin 15) + ((-740434800000) * v (2 : Fin 15) + ((-296173920000) * v (3 : Fin 15) + ((-222130440000) * v (4 : Fin 15) + ((29617392000) * v (5 : Fin 15) + ((192513048000) * v (7 : Fin 15))))))) =
      (![ 444260880000,592347840000,-740434800000,-296173920000,-222130440000,29617392000,0,192513048000,0,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral7]
  · change (-403536966000) * v (0 : Fin 15) + ((-481899649000) * v (1 : Fin 15) + ((616411971000) * v (2 : Fin 15) + ((156725366000) * v (3 : Fin 15) + ((185725729000) * v (4 : Fin 15) + ((-25298189000) * v (5 : Fin 15) + ((-48128262000) * v (6 : Fin 15) + ((192513048000) * v (8 : Fin 15)))))))) =
      (![ -403536966000,-481899649000,616411971000,156725366000,185725729000,-25298189000,-48128262000,0,192513048000,0,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral8]
  · change (-7641287136000) * v (0 : Fin 15) + ((-8648278464000) * v (1 : Fin 15) + ((11195374176000) * v (2 : Fin 15) + ((2013982656000) * v (3 : Fin 15) + ((3243104424000) * v (4 : Fin 15) + ((-355408704000) * v (5 : Fin 15) + ((1155078288000) * v (6 : Fin 15) + ((192513048000) * v (9 : Fin 15)))))))) =
      (![ -7641287136000,-8648278464000,11195374176000,2013982656000,3243104424000,-355408704000,1155078288000,0,0,192513048000,0,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral9]
  · change (-17326174320000) * v (0 : Fin 15) + ((-19507988864000) * v (1 : Fin 15) + ((25283380304000) * v (2 : Fin 15) + ((4363629088000) * v (3 : Fin 15) + ((5839562456000) * v (4 : Fin 15) + ((385026096000) * v (5 : Fin 15) + ((2310156576000) * v (6 : Fin 15) + ((192513048000) * v (10 : Fin 15)))))))) =
      (![ -17326174320000,-19507988864000,25283380304000,4363629088000,5839562456000,385026096000,2310156576000,0,0,0,192513048000,0,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral10]
  · change (-9050427114750) * v (0 : Fin 15) + ((-10214298066000) * v (1 : Fin 15) + ((13231107104250) * v (2 : Fin 15) + ((2327741902500) * v (3 : Fin 15) + ((3658904841375) * v (4 : Fin 15) + ((-280902452250) * v (5 : Fin 15) + ((156416851500) * v (6 : Fin 15) + ((-219585195375) * v (7 : Fin 15) + ((957064867200) * v (8 : Fin 15) + ((-233422070700) * v (9 : Fin 15) + ((52425428250) * v (10 : Fin 15) + ((192513048000) * v (11 : Fin 15)))))))))))) =
      (![ -9050427114750,-10214298066000,13231107104250,2327741902500,3658904841375,-280902452250,156416851500,-219585195375,957064867200,-233422070700,52425428250,192513048000,0,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral7, finSuccToNumeral8,
        finSuccToNumeral9, finSuccToNumeral10, finSuccToNumeral11]
  · change (37885975498560) * v (0 : Fin 15) + ((42957855153920) * v (1 : Fin 15) + ((-55586513653440) * v (2 : Fin 15) + ((-10143759310720) * v (3 : Fin 15) + ((-14918181625760) * v (4 : Fin 15) + ((817242569920) * v (5 : Fin 15) + ((-929196311680) * v (6 : Fin 15) + ((1383527104960) * v (7 : Fin 15) + ((-1675633569792) * v (8 : Fin 15) + ((992853959552) * v (9 : Fin 15) + ((-206630671520) * v (10 : Fin 15) + ((192513048000) * v (12 : Fin 15)))))))))))) =
      (![ 37885975498560,42957855153920,-55586513653440,-10143759310720,-14918181625760,817242569920,-929196311680,1383527104960,-1675633569792,992853959552,-206630671520,0,192513048000,0,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral7, finSuccToNumeral8,
        finSuccToNumeral9, finSuccToNumeral10, finSuccToNumeral12]
  · change (-23505925999500) * v (0 : Fin 15) + ((-26630736419000) * v (1 : Fin 15) + ((34466045085500) * v (2 : Fin 15) + ((6249620839000) * v (3 : Fin 15) + ((8869610345750) * v (4 : Fin 15) + ((-202479259500) * v (5 : Fin 15) + ((1130216451000) * v (6 : Fin 15) + ((-662860448250) * v (7 : Fin 15) + ((1234028390400) * v (8 : Fin 15) + ((-749497967400) * v (9 : Fin 15) + ((132096315000) * v (10 : Fin 15) + ((370135584000) * v (11 : Fin 15) + ((69799275000) * v (12 : Fin 15) + ((192513048000) * v (13 : Fin 15)))))))))))))) =
      (![ -23505925999500,-26630736419000,34466045085500,6249620839000,8869610345750,-202479259500,1130216451000,-662860448250,1234028390400,-749497967400,132096315000,370135584000,69799275000,192513048000,0 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral7, finSuccToNumeral8,
        finSuccToNumeral9, finSuccToNumeral10, finSuccToNumeral11, finSuccToNumeral12,
        finSuccToNumeral13]
  · change (11411353647750) * v (0 : Fin 15) + ((12880489244000) * v (1 : Fin 15) + ((-16684273793250) * v (2 : Fin 15) + ((-2938271192500) * v (3 : Fin 15) + ((-4129336239875) * v (4 : Fin 15) + ((-33385766750) * v (5 : Fin 15) + ((-1072665639500) * v (6 : Fin 15) + ((190859771375) * v (7 : Fin 15) + ((308653363200) * v (8 : Fin 15) + ((310598588300) * v (9 : Fin 15) + ((-72311807750) * v (10 : Fin 15) + ((346813376000) * v (11 : Fin 15) + ((302654625000) * v (12 : Fin 15) + ((333900112000) * v (13 : Fin 15) + ((192513048000) * v (14 : Fin 15))))))))))))))) =
      (![ 11411353647750,12880489244000,-16684273793250,-2938271192500,-4129336239875,-33385766750,-1072665639500,190859771375,308653363200,310598588300,-72311807750,346813376000,302654625000,333900112000,192513048000 ] : Fin 15 → ℤ) ⬝ᵥ v
    simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral1, finSuccToNumeral2, finSuccToNumeral3, finSuccToNumeral4,
        finSuccToNumeral5, finSuccToNumeral6, finSuccToNumeral7, finSuccToNumeral8,
        finSuccToNumeral9, finSuccToNumeral10, finSuccToNumeral11, finSuccToNumeral12,
        finSuccToNumeral13, finSuccToNumeral14]

theorem outInt_eq (v : Fin 15 → ℤ) : outInt v = bInt ⬝ᵥ v := by
  change (2506) * v (6 : Fin 15) + ((1282) * v (7 : Fin 15) + ((5844) * v (8 : Fin 15) + ((2506) * v (9 : Fin 15) + ((1282) * v (10 : Fin 15) + ((5068) * v (11 : Fin 15) + ((3675) * v (12 : Fin 15) + ((5068) * v (13 : Fin 15) + ((5844) * v (14 : Fin 15))))))))) =
    (![ 0,0,0,0,0,0,2506,1282,5844,2506,1282,5068,3675,5068,5844 ] : Fin 15 → ℤ) ⬝ᵥ v
  simp only [Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, zero_mul, zero_add, add_zero,
        finSuccToNumeral6, finSuccToNumeral7, finSuccToNumeral8, finSuccToNumeral9,
        finSuccToNumeral10, finSuccToNumeral11, finSuccToNumeral12, finSuccToNumeral13,
        finSuccToNumeral14]

-- The same closed test as checkScaledOrder. Only the lists are split.
def paidTree (t : FiniteRootedTree) : Bool :=
  decide ((t.factorial : ℤ) * outInt (replayStage actInt t) =
    33075 * 1540104384000 ^ ((t.order : ℕ) - 1))

theorem all_true_parts (k : ℕ) (trees : List FiniteRootedTree)
    (head : (trees.take k).all paidTree = true)
    (tail : (trees.drop k).all paidTree = true) : trees.all paidTree = true := by
  calc
    trees.all paidTree = (trees.take k ++ trees.drop k).all paidTree := by
      rw [List.take_append_drop]
    _ = true := by simp only [List.all_append, head, tail, Bool.true_and]

end RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper
