module

public import RKCert.ReviewedNative.CanonicalStageMemo
public import RKCert.ReviewedNative.QuadraticHornerReplay

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Quartic/quadratic integer numerators for Lobatto DIRK(10,9)

The inner generator is `x = (21/2)t` and satisfies the monic quartic
`x^4 - 147*x^2 + 3087 = 0`. The outer generator squares to seven.
The stage action uses only nonzero entries of the physical tableau. -/

namespace RKResearch.Certified.LobattoDIRK109

open RKResearch CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix

abbrev Count := 486

def innerMod : List ℤ := [3087,0,-147,0,1]
def stageDen : ℤ := 87572016
def weightDen : ℤ := 120

/-- Specialize quadratic multiplication to the pure relation `y^2=7`,
so no unused outer-linear factor enters the certificate word. -/
def mulQ (a b : QExpr) : QExpr :=
  ⟨.add (.mul a.re b.re) (.mul (.atom [7]) (.mul a.im b.im)),
    .add (.mul a.re b.im) (.mul a.im b.re)⟩

theorem mulQ_val {K : Type*} [CommRing K] {x y : K} (hy : y^2 = 7) (a b : QExpr) :
    (mulQ a b).val x y = a.val x y*b.val x y := by
  have h7 : coeval [7] x = 7 := by simp [coeval,horner]
  simp only [mulQ, QExpr.val, Expr.val, h7]
  calc
    _ = Expr.val x a.re * Expr.val x b.re +
        y*(Expr.val x a.re * Expr.val x b.im + Expr.val x a.im * Expr.val x b.re) +
        y^2*(Expr.val x a.im * Expr.val x b.im) := by rw [hy]; ring
    _ = _ := by ring

def rawA : Fin 10 → Fin 10 → QExpr := fun i j =>
  match i.val, j.val with
  | 1, 0 => ⟨(.mul (.atom [521262]) (.atom [21, -1])), (.mul (.atom [3546]) (.atom [0, -147, 0, 1]))⟩
  | 1, 1 => ⟨(.mul (.atom [521262]) (.atom [21, -1])), (.mul (.atom [3546]) (.atom [0, -147, 0, 1]))⟩
  | 2, 1 => ⟨(.mul (.atom [2085048]) (.atom [21, -1])), (.mul (.atom [14184]) (.atom [0, -147, 0, 1]))⟩
  | 3, 0 => ⟨(.mul (.atom [347508]) (.atom [21, -1])), (.mul (.atom [2364]) (.atom [0, -147, 0, 1]))⟩
  | 3, 1 => ⟨(.mul (.atom [1390032]) (.atom [21, -1])), (.mul (.atom [9456]) (.atom [0, -147, 0, 1]))⟩
  | 3, 2 => ⟨(.mul (.atom [347508]) (.atom [21, -1])), (.mul (.atom [2364]) (.atom [0, -147, 0, 1]))⟩
  | 4, 0 => ⟨(.mul (.atom [16548]) (.atom [7497, 1617, 0, -8])), (.mul (.atom [49644]) (.atom [882, 203, 0, -1]))⟩
  | 4, 1 => ⟨(.mul (.atom [66192]) (.atom [-3969, -903, 0, 4])), (.mul (.atom [28368]) (.atom [-4116, -931, 0, 5]))⟩
  | 4, 2 => ⟨(.mul (.atom [16548]) (.atom [-3969, -903, 0, 4])), (.mul (.atom [7092]) (.atom [-4116, -931, 0, 5]))⟩
  | 4, 3 => ⟨(.mul (.atom [49644]) (.atom [5145, 1092, 0, -5])), (.mul (.atom [7092]) (.atom [13377, 3234, 0, -17]))⟩
  | 4, 4 => ⟨(.mul (.atom [49644]) (.atom [-147, -84, 0, 1])), (.mul (.atom [21276]) (.atom [343, 98, 0, -1]))⟩
  | 5, 0 => ⟨(.mul (.atom [5516]) (.atom [60123, 11991, -476, -100])), (.mul (.atom [788]) (.atom [158466, 31899, -1274, -265]))⟩
  | 5, 1 => ⟨(.mul (.atom [22064]) (.atom [-36897, -7287, 322, 58])), (.mul (.atom [3152]) (.atom [-94668, -18375, 784, 151]))⟩
  | 5, 2 => ⟨(.mul (.atom [5516]) (.atom [-36897, -7287, 322, 58])), (.mul (.atom [788]) (.atom [-94668, -18375, 784, 151]))⟩
  | 5, 3 => ⟨(.mul (.atom [38612]) (.atom [17913, 3546, -146, -29])), (.mul (.atom [788]) (.atom [328251, 65268, -2702, -533]))⟩
  | 5, 4 => ⟨(.mul (.atom [22064]) (.atom [2058, 0, -28, 1])), (.mul (.atom [1576]) (.atom [-2058, 0, 28, -1]))⟩
  | 5, 5 => ⟨(.mul (.atom [49644]) (.atom [-147, -84, 0, 1])), (.mul (.atom [21276]) (.atom [-343, -98, 0, 1]))⟩
  | 6, 0 => ⟨(.mul (.atom [5516]) (.atom [-27636, -5586, 217, 48])), (.mul (.atom [788]) (.atom [-66885, -14406, 427, 129]))⟩
  | 6, 1 => ⟨(.mul (.atom [22064]) (.atom [14112, 3150, -105, -26])), (.mul (.atom [3152]) (.atom [52479, 8820, -609, -59]))⟩
  | 6, 2 => ⟨(.mul (.atom [5516]) (.atom [14112, 3150, -105, -26])), (.mul (.atom [788]) (.atom [52479, 8820, -609, -59]))⟩
  | 6, 3 => ⟨(.mul (.atom [2758]) (.atom [-102165, -21210, 805, 178])), (.mul (.atom [394]) (.atom [-320019, -60270, 2905, 478]))⟩
  | 6, 4 => ⟨(.mul (.atom [2758]) (.atom [13671, 882, -189, 4])), (.mul (.atom [2758]) (.atom [-7497, -630, 189, -8]))⟩
  | 6, 5 => ⟨(.mul (.atom [8274]) (.atom [3087, 462, 21, -8])), (.mul (.atom [74466]) (.atom [-49, -14, 3]))⟩
  | 6, 6 => ⟨(.mul (.atom [8274]) (.atom [3087, -210, -21, 2])), (.mul (.atom [3546]) (.atom [-1029, 294, 49, -6]))⟩
  | 7, 0 => ⟨(.mul (.atom [5516]) (.atom [-236523, -46935, 1862, 360])), (.mul (.atom [5516]) (.atom [-89376, -17703, 718, 135]))⟩
  | 7, 1 => ⟨(.mul (.atom [66192]) (.atom [45717, 9387, -322, -76])), (.mul (.atom [9456]) (.atom [121422, 25137, -770, -209]))⟩
  | 7, 2 => ⟨(.mul (.atom [16548]) (.atom [45717, 9387, -322, -76])), (.mul (.atom [2364]) (.atom [121422, 25137, -770, -209]))⟩
  | 7, 3 => ⟨(.mul (.atom [16548]) (.atom [-159642, -32466, 1197, 257])), (.mul (.atom [2364]) (.atom [-426006, -85260, 3087, 677]))⟩
  | 7, 4 => ⟨(.mul (.atom [84]) (.atom [-171843, -15666, -6713, 782])), (.mul (.atom [12]) (.atom [-173901, -311934, -59311, 8032]))⟩
  | 7, 5 => ⟨(.mul (.atom [38612]) (.atom [3759, 474, -61])), (.mul (.atom [5516]) (.atom [8967, 966, -179]))⟩
  | 7, 6 => ⟨(.mul (.atom [38612]) (.atom [1617, 138, -19])), (.mul (.atom [38612]) (.atom [399, 114, -11]))⟩
  | 7, 7 => ⟨(.mul (.atom [84]) (.atom [171843, -9156, 2576, -191])), (.mul (.atom [12]) (.atom [173901, -151410, -2744, 1227]))⟩
  | 8, 0 => ⟨(.mul (.atom [16548]) (.atom [27783, 4998, -378, -29])), (.mul (.atom [16548]) (.atom [10143, 1932, -114, -13]))⟩
  | 8, 1 => ⟨(.mul (.atom [66192]) (.atom [-9261, -3234, -84, 41])), (.mul (.atom [66192]) (.atom [-6615, -1218, 42, 11]))⟩
  | 8, 2 => ⟨(.mul (.atom [16548]) (.atom [-9261, -3234, -84, 41])), (.mul (.atom [16548]) (.atom [-6615, -1218, 42, 11]))⟩
  | 8, 3 => ⟨(.mul (.atom [8274]) (.atom [97461, 21756, -588, -197])), (.mul (.atom [8274]) (.atom [43218, 8085, -363, -65]))⟩
  | 8, 4 => ⟨(.mul (.atom [42]) (.atom [-6830649, 44247, 238371, -16859])), (.mul (.atom [42]) (.atom [1487052, 49476, -17940, 103]))⟩
  | 8, 5 => ⟨(.mul (.atom [8274]) (.atom [-19845, -294, 630, -41])), (.mul (.atom [8274]) (.atom [-5292, 357, 225, -19]))⟩
  | 8, 6 => ⟨(.mul (.atom [24822]) (.atom [-4557, 294, 154, -13])), (.mul (.atom [24822]) (.atom [588, -231, 5, 1]))⟩
  | 8, 7 => ⟨(.mul (.atom [42]) (.atom [488628, -44247, -23247, 2084])), (.mul (.atom [42]) (.atom [-270774, 62223, 4347, -694]))⟩
  | 8, 8 => ⟨.atom [43786008], .atom []⟩
  | 9, 0 => ⟨(.mul (.atom [8274]) (.atom [193599, 39102, -1638, -319])), (.mul (.atom [8274]) (.atom [72765, 14574, -600, -119]))⟩
  | 9, 1 => ⟨(.mul (.atom [33096]) (.atom [-114219, -22344, 882, 187])), (.mul (.atom [33096]) (.atom [-45423, -8862, 378, 73]))⟩
  | 9, 2 => ⟨(.mul (.atom [8274]) (.atom [-114219, -22344, 882, 187])), (.mul (.atom [8274]) (.atom [-45423, -8862, 378, 73]))⟩
  | 9, 3 => ⟨(.mul (.atom [12411]) (.atom [267981, 52332, -2156, -431])), (.mul (.atom [12411]) (.atom [101724, 20265, -845, -167]))⟩
  | 9, 4 => ⟨(.mul (.atom [21]) (.atom [-5532786, 36897, 81753, -4378])), (.mul (.atom [21]) (.atom [2859003, 360150, -31494, -1792]))⟩
  | 9, 5 => ⟨(.mul (.atom [86877]) (.atom [-1407, -378, 22, 3])), (.mul (.atom [12411]) (.atom [-2058, -567, 23, 3]))⟩
  | 9, 6 => ⟨(.mul (.atom [4137]) (.atom [1323, -3234, 126, 17])), (.mul (.atom [4137]) (.atom [-2646, -987, 27, 7]))⟩
  | 9, 7 => ⟨(.mul (.atom [21]) (.atom [4577139, -152733, -15561, 635])), (.mul (.atom [147]) (.atom [-60921, -13035, 531, 59]))⟩
  | 9, 8 => ⟨.atom [21893004], .atom []⟩
  | _,_ => QExpr.zero

def rawB : Fin 10 → QExpr := fun i =>
  match i.val with
  | 0 => ⟨.atom [2], .atom []⟩
  | 3 => ⟨.atom [28], .atom [-2]⟩
  | 4 => ⟨.atom [14], .atom [-1]⟩
  | 5 => ⟨.atom [28], .atom [2]⟩
  | 6 => ⟨.atom [28], .atom [2]⟩
  | 7 => ⟨.atom [14], .atom [-1]⟩
  | 8 => ⟨.atom [2], .atom []⟩
  | 9 => ⟨.atom [4], .atom []⟩
  | _ => QExpr.zero

def Vec := Fin 10 → QExpr

def VecVal {K : Type*} [CommRing K] (x y : K) (v : Vec) (i : Fin 10) : K :=
  (v i).val x y

def numA {K : Type*} [CommRing K] (x y : K) : Matrix (Fin 10) (Fin 10) K :=
  Matrix.of fun i j => (rawA i j).val x y

def act (v : Vec) : Vec := fun i =>
  match i.val with
  | 0 => QExpr.zero
  | 1 => (mulQ (rawA 1 0) (v 0)).add ((mulQ (rawA 1 1) (v 1)))
  | 2 => (mulQ (rawA 2 1) (v 1))
  | 3 => (mulQ (rawA 3 0) (v 0)).add ((mulQ (rawA 3 1) (v 1)).add ((mulQ (rawA 3 2) (v 2))))
  | 4 => (mulQ (rawA 4 0) (v 0)).add ((mulQ (rawA 4 1) (v 1)).add ((mulQ (rawA 4 2) (v 2)).add ((mulQ (rawA 4 3) (v 3)).add ((mulQ (rawA 4 4) (v 4))))))
  | 5 => (mulQ (rawA 5 0) (v 0)).add ((mulQ (rawA 5 1) (v 1)).add ((mulQ (rawA 5 2) (v 2)).add ((mulQ (rawA 5 3) (v 3)).add ((mulQ (rawA 5 4) (v 4)).add ((mulQ (rawA 5 5) (v 5)))))))
  | 6 => (mulQ (rawA 6 0) (v 0)).add ((mulQ (rawA 6 1) (v 1)).add ((mulQ (rawA 6 2) (v 2)).add ((mulQ (rawA 6 3) (v 3)).add ((mulQ (rawA 6 4) (v 4)).add ((mulQ (rawA 6 5) (v 5)).add ((mulQ (rawA 6 6) (v 6))))))))
  | 7 => (mulQ (rawA 7 0) (v 0)).add ((mulQ (rawA 7 1) (v 1)).add ((mulQ (rawA 7 2) (v 2)).add ((mulQ (rawA 7 3) (v 3)).add ((mulQ (rawA 7 4) (v 4)).add ((mulQ (rawA 7 5) (v 5)).add ((mulQ (rawA 7 6) (v 6)).add ((mulQ (rawA 7 7) (v 7)))))))))
  | 8 => (mulQ (rawA 8 0) (v 0)).add ((mulQ (rawA 8 1) (v 1)).add ((mulQ (rawA 8 2) (v 2)).add ((mulQ (rawA 8 3) (v 3)).add ((mulQ (rawA 8 4) (v 4)).add ((mulQ (rawA 8 5) (v 5)).add ((mulQ (rawA 8 6) (v 6)).add ((mulQ (rawA 8 7) (v 7)).add ((mulQ (rawA 8 8) (v 8))))))))))
  | 9 => (mulQ (rawA 9 0) (v 0)).add ((mulQ (rawA 9 1) (v 1)).add ((mulQ (rawA 9 2) (v 2)).add ((mulQ (rawA 9 3) (v 3)).add ((mulQ (rawA 9 4) (v 4)).add ((mulQ (rawA 9 5) (v 5)).add ((mulQ (rawA 9 6) (v 6)).add ((mulQ (rawA 9 7) (v 7)).add ((mulQ (rawA 9 8) (v 8))))))))))
  | _ => QExpr.zero

set_option maxHeartbeats 3500000 in
theorem act_val {K : Type*} [CommRing K] {x y : K} (hy : y^2 = 7) (v : Vec) :
    VecVal x y (act v) = numA x y *ᵥ VecVal x y v := by
  funext i
  fin_cases i <;> simp [act, mulQ_val hy (x := x), QExpr.val_add, QExpr.val_zero, numA, rawA,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, VecVal, add_assoc]

def point (v w : Vec) : Vec := fun i => mulQ (v i) (w i)

theorem point_val {K : Type*} [CommRing K] {x y : K} (hy : y^2 = 7) (v w : Vec) :
    VecVal x y (point v w) = VecVal x y v * VecVal x y w := by
  funext i
  exact mulQ_val hy _ _

def sumWord (v : Vec) : QExpr :=
  (mulQ (rawB 0) (v 0)).add ((mulQ (rawB 3) (v 3)).add ((mulQ (rawB 4) (v 4)).add ((mulQ (rawB 5) (v 5)).add ((mulQ (rawB 6) (v 6)).add ((mulQ (rawB 7) (v 7)).add ((mulQ (rawB 8) (v 8)).add ((mulQ (rawB 9) (v 9)))))))))

theorem sumWord_val {K : Type*} [CommRing K] {x y : K} (hy : y^2 = 7) (v : Vec) :
    (sumWord v).val x y = VecVal x y rawB ⬝ᵥ VecVal x y v := by
  simp [sumWord, mulQ_val hy (x := x), QExpr.val_add, QExpr.val_zero, rawB,
    dotProduct, Fin.sum_univ_succ, VecVal, add_assoc]

end RKResearch.Certified.LobattoDIRK109
