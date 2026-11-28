import Lean.Elab.Tactic.Omega

/-! A portable kernel receipt for the final scalar gates and modular
Bézout certificates of the fourth-supported mask. The formal stage-space
argument, rational eliminants, and construction of the modular data are
separate analytic/reproducible components. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.FourthMaskCore

theorem betaGuard (beta step gap ell slope chi big diag : Int)
    (hstep : step ≠ 0) (hgap : gap ≠ 0) (hbig : big ≠ 0)
    (row : step*ell=beta*diag)
    (top : beta=0 → chi*big=slope)
    (compare : beta=0 → ell=0 → slope*gap=0)
    (unitCase : slope=0 → chi≠0) : beta≠0 := by
  intro h
  have h1 : step*ell=0 := by simpa [h] using row
  have hl : ell=0 := (Int.mul_eq_zero.mp h1).resolve_left hstep
  have h2 : slope=0 := (Int.mul_eq_zero.mp (compare h hl)).resolve_right hgap
  have h3 : chi*big=0 := by simpa [h2] using top h
  exact (Int.mul_eq_zero.mp h3).elim (unitCase h2) hbig

theorem leadingSlopeCancellation (num den coeff : Int) (hden : den≠0)
    (cleared : (den+num)*coeff=num*coeff) : coeff=0 := by
  rw [Int.add_mul] at cleared
  have h : den*coeff=0 := by omega
  exact (Int.mul_eq_zero.mp h).resolve_left hden

def base : Int := 1048576

def pack (xs : List Int) : Int :=
  xs.foldr (fun z n => z + base*n) 0

def residues (p : Int) : Nat → Int → List Int
  | 0, _ => []
  | n+1, x => ((x%base)%p) :: residues p n (x/base)

def atScalar (a : List (List Int)) (i : Nat) : Int :=
  pack (a[i]?.getD [])

def prod (a b : List (List Int)) (i : Nat) : Int :=
  (List.range (i+1)).foldl (fun t j => t+atScalar a j*atScalar b (i-j)) 0

/-- Inputs are represented coefficientwise in [0,p), and each sum has at
most six products. The bound prevents carries between coefficients. -/
def check (p : Int) (d : Nat) (a b : Int) : Bool :=
  6 * (Int.ofNat d+1) * (p-1)^2 < base &&
  residues p (2*d+2) a == residues p (2*d+2) b

def small (p : Int) (xs : List (List Int)) : Bool :=
  xs.all (fun x => x.all (fun v => 0≤v && v<p))
def f0 : List Int := [1, 14, 2, 8, 5, 6, 1, 2, 4, 4, 4, 11, 2, 1]
def A0 : List (List Int) := [[6, 6, 4, 11, 1, 0, 4, 1, 9, 8, 4, 15, 13], [10, 15, 16, 9, 10, 6, 16, 6, 0, 5, 2, 2, 8], [8, 11, 15, 7, 5, 13, 4, 6, 2, 12, 3, 4, 3]]
def B0 : List (List Int) := [[16, 5, 14, 7, 5, 14, 14, 13, 1, 2, 6, 1, 4], [15, 3, 1, 8, 3, 14, 12, 9, 9, 8, 15, 15, 9], [5, 11, 2, 6, 11, 2, 14, 4, 14, 15, 14, 13, 8], [0, 9, 5, 7, 3, 5, 10, 14, 15, 12, 0, 14, 9]]
def S0 : List (List Int) := [[16, 6, 2, 11, 15, 15, 3, 7, 8, 7, 9, 16, 8], [16, 9, 8, 12, 4, 15, 5, 4, 9, 10, 11, 14, 9], [13, 8, 13, 7, 4, 6, 0, 2, 8, 5, 6, 6, 0]]
def T0 : List (List Int) := [[2, 0, 8, 5, 11, 14, 5, 2, 4, 15, 12, 12, 16], [15, 14, 0, 16, 14, 5, 3, 11, 8, 6, 7, 16, 1]]
def a0 : List Int := [2, 1, 0, 13, 12, 8, 13, 5, 10, 10, 1, 14, 12]
def ai0 : List Int := [11, 8, 6, 4, 14, 3, 2, 13, 6, 10, 14, 13, 11]
def ti0 : List Int := [15, 3, 5, 16, 1, 4, 10, 15, 3, 12, 8, 16, 16]
theorem ranges0 : small 17 ([f0,a0,ai0,ti0] ++ A0 ++ B0 ++ S0 ++ T0) = true := by decide +kernel
theorem unit00 : check 17 13 ((pack a0)*(pack ai0)) (pack f0*pack [4, 5, 10, 9, 11, 15, 1, 11, 3, 7, 12, 13]+1) = true := by decide +kernel
theorem unit01 : check 17 13 ((atScalar A0 2)*(pack ti0)) (pack f0*pack [0, 2, 15, 0, 3, 16, 7, 9, 6, 1, 16, 14]+1) = true := by decide +kernel
theorem bezout00 : check 17 13 (prod A0 S0 0 + prod B0 T0 0) (pack f0*pack [8, 13, 2, 5, 11, 1, 12, 12, 15, 13, 5, 15] + 1) = true := by decide +kernel
theorem bezout01 : check 17 13 (prod A0 S0 1 + prod B0 T0 1) (pack f0*pack [16, 4, 13, 12, 13, 5, 14, 15, 4, 11, 12, 6] + 0) = true := by decide +kernel
theorem bezout02 : check 17 13 (prod A0 S0 2 + prod B0 T0 2) (pack f0*pack [6, 6, 7, 14, 14, 6, 3, 10, 12, 16, 13, 12] + 0) = true := by decide +kernel
theorem bezout03 : check 17 13 (prod A0 S0 3 + prod B0 T0 3) (pack f0*pack [10, 7, 2, 15, 7, 10, 16, 2, 12, 13, 3, 9] + 0) = true := by decide +kernel
theorem bezout04 : check 17 13 (prod A0 S0 4 + prod B0 T0 4) (pack f0*pack [2, 8, 13, 14, 8, 14, 13, 1, 13, 16, 5, 9] + 0) = true := by decide +kernel
def f1 : List Int := [1, 11, 4, 16, 16, 7, 13, 12, 15, 14, 4, 12, 13, 1]
def A1 : List (List Int) := [[1, 13, 15, 3, 6, 11, 13, 16, 7, 8, 16, 11, 9], [2, 1, 14, 4, 12, 1, 16, 9, 12, 2, 13, 8, 14], [3, 3, 5, 16, 15, 1, 10, 7, 6, 9, 0, 8, 2]]
def B1 : List (List Int) := [[6, 11, 10, 15, 10, 13, 13, 14, 10, 11, 16, 6, 9], [10, 0, 15, 6, 7, 8, 10, 14, 1, 12, 9, 15, 9], [5, 3, 2, 5, 8, 0, 14, 10, 5, 1, 5, 5, 0], [12, 12, 0, 15, 14, 5, 12, 2, 1, 2, 3, 1, 0]]
def S1 : List (List Int) := [[3, 1, 8, 14, 10, 16, 2, 3, 14, 11, 13, 9, 6], [9, 1, 3, 12, 14, 9, 15, 3, 8, 3, 8, 3, 5], [1, 13, 11, 0, 2, 8, 5, 3, 8, 12, 0, 10, 15]]
def T1 : List (List Int) := [[3, 13, 8, 1, 0, 8, 13, 1, 13, 16, 14, 1, 1], [13, 2, 8, 0, 4, 15, 13, 0, 12, 8, 7, 12, 9]]
def a1 : List Int := [16, 2, 16, 10, 14, 10, 8, 13, 1, 16, 11, 3, 12]
def ai1 : List Int := [9, 13, 2, 7, 6, 8, 6, 4, 16, 0, 6, 12, 2]
def ti1 : List Int := [3, 14, 2, 13, 8, 13, 8, 13, 6, 2, 8, 7, 8]
theorem ranges1 : small 17 ([f1,a1,ai1,ti1] ++ A1 ++ B1 ++ S1 ++ T1) = true := by decide +kernel
theorem unit10 : check 17 13 ((pack a1)*(pack ai1)) (pack f1*pack [7, 13, 14, 11, 3, 3, 0, 16, 13, 10, 8, 7]+1) = true := by decide +kernel
theorem unit11 : check 17 13 ((atScalar A1 2)*(pack ti1)) (pack f1*pack [8, 14, 13, 6, 8, 11, 15, 16, 11, 6, 6, 16]+1) = true := by decide +kernel
theorem bezout10 : check 17 13 (prod A1 S1 0 + prod B1 T1 0) (pack f1*pack [3, 16, 14, 9, 3, 9, 16, 0, 8, 0, 6, 12] + 1) = true := by decide +kernel
theorem bezout11 : check 17 13 (prod A1 S1 1 + prod B1 T1 1) (pack f1*pack [4, 7, 0, 11, 15, 0, 4, 3, 7, 3, 9, 15] + 0) = true := by decide +kernel
theorem bezout12 : check 17 13 (prod A1 S1 2 + prod B1 T1 2) (pack f1*pack [3, 8, 1, 12, 9, 6, 12, 9, 9, 2, 7, 9] + 0) = true := by decide +kernel
theorem bezout13 : check 17 13 (prod A1 S1 3 + prod B1 T1 3) (pack f1*pack [11, 7, 3, 9, 7, 14, 3, 11, 0, 9, 8, 16] + 0) = true := by decide +kernel
theorem bezout14 : check 17 13 (prod A1 S1 4 + prod B1 T1 4) (pack f1*pack [6, 3, 4, 15, 15, 5, 10, 5, 8, 2, 14, 13] + 0) = true := by decide +kernel
def f2 : List Int := [6, 15, 13, 12, 1]
def A2 : List (List Int) := [[3, 14, 2, 6], [13, 5, 7, 4], [5, 8, 4, 9]]
def B2 : List (List Int) := [[14, 11, 0, 8], [11, 8, 11, 1], [2, 4, 3, 1], [2, 1, 13, 8]]
def S2 : List (List Int) := [[0, 16, 0, 12], [1, 13, 1, 5], [10, 10, 0, 7]]
def T2 : List (List Int) := [[4, 11, 11, 11], [6, 9, 15, 5]]
def a2 : List Int := [14, 3, 2, 7]
def ai2 : List Int := [5, 11, 4, 7]
def ti2 : List Int := [1, 3, 16, 10]
theorem ranges2 : small 17 ([f2,a2,ai2,ti2] ++ A2 ++ B2 ++ S2 ++ T2) = true := by decide +kernel
theorem unit20 : check 17 4 ((pack a2)*(pack ai2)) (pack f2*pack [3, 15, 15]+1) = true := by decide +kernel
theorem unit21 : check 17 4 ((atScalar A2 2)*(pack ti2)) (pack f2*pack [12, 5, 5]+1) = true := by decide +kernel
theorem bezout20 : check 17 4 (prod A2 S2 0 + prod B2 T2 0) (pack f2*pack [12, 11, 7] + 1) = true := by decide +kernel
theorem bezout21 : check 17 4 (prod A2 S2 1 + prod B2 T2 1) (pack f2*pack [2, 11, 10] + 0) = true := by decide +kernel
theorem bezout22 : check 17 4 (prod A2 S2 2 + prod B2 T2 2) (pack f2*pack [11, 6, 16] + 0) = true := by decide +kernel
theorem bezout23 : check 17 4 (prod A2 S2 3 + prod B2 T2 3) (pack f2*pack [6, 13, 13] + 0) = true := by decide +kernel
theorem bezout24 : check 17 4 (prod A2 S2 4 + prod B2 T2 4) (pack f2*pack [16, 14, 1] + 0) = true := by decide +kernel
def f3 : List Int := [10, 16, 5, 16, 1]
def A3 : List (List Int) := [[10, 12, 8, 15], [13, 4, 15, 2], [8, 11, 4, 0]]
def B3 : List (List Int) := [[13, 3, 7, 11], [5, 10, 9, 10], [9, 16, 4, 5], [10, 13, 6, 14]]
def S3 : List (List Int) := [[13, 6, 9, 11], [12, 14, 7, 12], [11, 10, 3, 1]]
def T3 : List (List Int) := [[11, 12, 11, 16], [3, 11, 4, 6]]
def a3 : List Int := [0, 6, 3, 14]
def ai3 : List Int := [1, 16, 7, 9]
def ti3 : List Int := [16, 14, 5, 13]
theorem ranges3 : small 17 ([f3,a3,ai3,ti3] ++ A3 ++ B3 ++ S3 ++ T3) = true := by decide +kernel
theorem unit30 : check 17 4 ((pack a3)*(pack ai3)) (pack f3*pack [5, 13, 7]+1) = true := by decide +kernel
theorem unit31 : check 17 4 ((atScalar A3 2)*(pack ti3)) (pack f3*pack [11, 1, 0]+1) = true := by decide +kernel
theorem bezout30 : check 17 4 (prod A3 S3 0 + prod B3 T3 0) (pack f3*pack [0, 15, 1] + 1) = true := by decide +kernel
theorem bezout31 : check 17 4 (prod A3 S3 1 + prod B3 T3 1) (pack f3*pack [6, 13, 3] + 0) = true := by decide +kernel
theorem bezout32 : check 17 4 (prod A3 S3 2 + prod B3 T3 2) (pack f3*pack [11, 3, 9] + 0) = true := by decide +kernel
theorem bezout33 : check 17 4 (prod A3 S3 3 + prod B3 T3 3) (pack f3*pack [7, 7, 1] + 0) = true := by decide +kernel
theorem bezout34 : check 17 4 (prod A3 S3 4 + prod B3 T3 4) (pack f3*pack [5, 10, 16] + 0) = true := by decide +kernel
def f4 : List Int := [14, 16, 14, 1, 1]
def A4 : List (List Int) := [[3, 11, 16, 2], [16, 10, 5, 9], [11, 13, 0, 11]]
def B4 : List (List Int) := [[18, 2, 10, 3], [1, 17, 6, 2], [18, 1, 14, 11], [11, 15, 2, 17]]
def S4 : List (List Int) := [[3, 17, 9, 16], [15, 11, 7, 2], [2, 11, 14, 14]]
def T4 : List (List Int) := [[0, 10, 13, 5], [7, 9, 13, 17]]
def a4 : List Int := [10, 3, 13, 3]
def ai4 : List Int := [11, 7, 7, 3]
def ti4 : List Int := [13, 5, 11, 10]
theorem ranges4 : small 19 ([f4,a4,ai4,ti4] ++ A4 ++ B4 ++ S4 ++ T4) = true := by decide +kernel
theorem unit40 : check 19 4 ((pack a4)*(pack ai4)) (pack f4*pack [1, 13, 9]+1) = true := by decide +kernel
theorem unit41 : check 19 4 ((atScalar A4 2)*(pack ti4)) (pack f4*pack [2, 11, 15]+1) = true := by decide +kernel
theorem bezout40 : check 19 4 (prod A4 S4 0 + prod B4 T4 0) (pack f4*pack [6, 12, 9] + 1) = true := by decide +kernel
theorem bezout41 : check 19 4 (prod A4 S4 1 + prod B4 T4 1) (pack f4*pack [17, 16, 0] + 0) = true := by decide +kernel
theorem bezout42 : check 19 4 (prod A4 S4 2 + prod B4 T4 2) (pack f4*pack [15, 17, 7] + 0) = true := by decide +kernel
theorem bezout43 : check 19 4 (prod A4 S4 3 + prod B4 T4 3) (pack f4*pack [0, 9, 2] + 0) = true := by decide +kernel
theorem bezout44 : check 19 4 (prod A4 S4 4 + prod B4 T4 4) (pack f4*pack [3, 4, 6] + 0) = true := by decide +kernel
def f5 : List Int := [2, 16, 17, 7, 1]
def A5 : List (List Int) := [[8, 7, 0, 7], [10, 0, 13, 5], [11, 9, 11, 9]]
def B5 : List (List Int) := [[7, 0, 14, 4], [7, 18, 16, 17], [7, 15, 13, 17], [1, 12, 11, 14]]
def S5 : List (List Int) := [[14, 0, 5, 15], [16, 11, 13, 11], [18, 12, 2, 4]]
def T5 : List (List Int) := [[14, 0, 13, 14], [7, 9, 2, 12]]
def a5 : List Int := [4, 12, 2, 14]
def ai5 : List Int := [7, 15, 14, 4]
def ti5 : List Int := [7, 4, 10, 6]
theorem ranges5 : small 19 ([f5,a5,ai5,ti5] ++ A5 ++ B5 ++ S5 ++ T5) = true := by decide +kernel
theorem unit50 : check 19 4 ((pack a5)*(pack ai5)) (pack f5*pack [4, 2, 18]+1) = true := by decide +kernel
theorem unit51 : check 19 4 ((atScalar A5 2)*(pack ti5)) (pack f5*pack [0, 6, 16]+1) = true := by decide +kernel
theorem bezout50 : check 19 4 (prod A5 S5 0 + prod B5 T5 0) (pack f5*pack [0, 11, 9] + 1) = true := by decide +kernel
theorem bezout51 : check 19 4 (prod A5 S5 1 + prod B5 T5 1) (pack f5*pack [8, 13, 1] + 0) = true := by decide +kernel
theorem bezout52 : check 19 4 (prod A5 S5 2 + prod B5 T5 2) (pack f5*pack [8, 13, 14] + 0) = true := by decide +kernel
theorem bezout53 : check 19 4 (prod A5 S5 3 + prod B5 T5 3) (pack f5*pack [10, 5, 6] + 0) = true := by decide +kernel
theorem bezout54 : check 19 4 (prod A5 S5 4 + prod B5 T5 4) (pack f5*pack [17, 10, 14] + 0) = true := by decide +kernel
def f6 : List Int := [16, 10, 15, 15, 3, 12, 0, 4, 1, 8, 9, 14, 11, 17, 0, 6, 17, 0, 11, 4, 8, 16, 7, 0, 1]
def A6 : List (List Int) := [[3, 14, 5, 0, 9, 0, 10, 18, 17, 10, 1, 15, 9, 0, 10, 6, 12, 0, 3, 10, 0, 14, 8, 2], [3, 0, 0, 8, 2, 2, 17, 13, 5, 3, 7, 12, 12, 13, 7, 18, 17, 11, 3, 9, 17, 8, 4, 14], [7, 17, 12, 2, 18, 8, 11, 17, 6, 14, 8, 4, 11, 12, 5, 3, 10, 13, 13, 13, 18, 3, 13, 11]]
def B6 : List (List Int) := [[16, 2, 13, 4, 3, 12, 16, 0, 3, 8, 18, 8, 10, 1, 4, 18, 18, 12, 12, 0, 15, 10, 10, 1], [6, 16, 2, 11, 2, 6, 5, 9, 9, 5, 5, 10, 8, 4, 17, 12, 1, 1, 8, 16, 3, 13, 17, 17], [18, 15, 11, 18, 7, 9, 4, 10, 5, 14, 4, 4, 12, 13, 15, 14, 7, 16, 10, 9, 7, 3, 15, 11], [14, 5, 5, 3, 6, 2, 13, 8, 16, 1, 5, 18, 16, 5, 11, 0, 15, 11, 9, 7, 13, 3, 17, 6]]
def S6 : List (List Int) := [[4, 1, 15, 3, 10, 1, 5, 8, 15, 7, 2, 5, 18, 2, 16, 3, 13, 0, 17, 17, 9, 6, 18, 5], [14, 18, 6, 0, 16, 11, 4, 12, 12, 18, 7, 11, 3, 18, 13, 5, 11, 13, 7, 0, 13, 13, 2, 12], [11, 9, 10, 16, 8, 17, 12, 7, 2, 11, 17, 15, 12, 10, 17, 1, 5, 16, 3, 5, 0, 7, 14, 9]]
def T6 : List (List Int) := [[6, 3, 17, 14, 9, 13, 11, 15, 15, 7, 10, 5, 18, 13, 17, 3, 2, 0, 18, 5, 1, 2, 0, 10], [6, 8, 18, 11, 3, 3, 17, 8, 16, 8, 11, 17, 11, 7, 5, 6, 15, 15, 12, 2, 17, 18, 11, 12]]
def a6 : List Int := [1, 12, 12, 11, 5, 11, 12, 12, 5, 1, 2, 1, 18, 9, 6, 17, 8, 0, 18, 17, 4, 0, 10, 14]
def ai6 : List Int := [11, 3, 2, 18, 9, 10, 11, 18, 8, 3, 1, 5, 0, 12, 17, 16, 1, 9, 9, 7, 14, 6, 12, 14]
def ti6 : List Int := [8, 9, 17, 6, 15, 9, 7, 13, 17, 3, 18, 18, 18, 17, 12, 4, 10, 2, 4, 15, 4, 12, 2, 16]
theorem ranges6 : small 19 ([f6,a6,ai6,ti6] ++ A6 ++ B6 ++ S6 ++ T6) = true := by decide +kernel
theorem unit60 : check 19 24 ((pack a6)*(pack ai6)) (pack f6*pack [3, 3, 0, 8, 2, 18, 13, 15, 1, 15, 2, 3, 9, 1, 18, 16, 4, 18, 0, 17, 10, 4, 6]+1) = true := by decide +kernel
theorem unit61 : check 19 24 ((atScalar A6 2)*(pack ti6)) (pack f6*pack [7, 14, 16, 13, 3, 12, 13, 5, 6, 17, 5, 9, 15, 17, 8, 16, 16, 12, 7, 1, 0, 2, 5]+1) = true := by decide +kernel
theorem bezout60 : check 19 24 (prod A6 S6 0 + prod B6 T6 0) (pack f6*pack [15, 4, 13, 1, 9, 5, 15, 3, 2, 12, 17, 9, 12, 3, 7, 18, 4, 16, 11, 1, 17, 5, 1] + 1) = true := by decide +kernel
theorem bezout61 : check 19 24 (prod A6 S6 1 + prod B6 T6 1) (pack f6*pack [14, 17, 7, 9, 2, 11, 7, 1, 15, 9, 9, 2, 9, 5, 6, 1, 7, 3, 12, 15, 7, 8, 10] + 0) = true := by decide +kernel
theorem bezout62 : check 19 24 (prod A6 S6 2 + prod B6 T6 2) (pack f6*pack [0, 16, 9, 10, 6, 14, 5, 16, 0, 9, 1, 11, 11, 16, 13, 7, 6, 9, 5, 4, 6, 11, 4] + 0) = true := by decide +kernel
theorem bezout63 : check 19 24 (prod A6 S6 3 + prod B6 T6 3) (pack f6*pack [0, 2, 10, 0, 16, 15, 12, 4, 7, 14, 10, 18, 13, 5, 10, 7, 5, 17, 0, 3, 2, 7, 13] + 0) = true := by decide +kernel
theorem bezout64 : check 19 24 (prod A6 S6 4 + prod B6 T6 4) (pack f6*pack [16, 5, 4, 7, 15, 18, 1, 8, 14, 1, 10, 10, 13, 16, 13, 3, 18, 1, 3, 12, 9, 9, 0] + 0) = true := by decide +kernel

#print axioms betaGuard
#print axioms leadingSlopeCancellation
#print axioms ranges0
#print axioms unit00
#print axioms unit01
#print axioms bezout00
#print axioms bezout01
#print axioms bezout02
#print axioms bezout03
#print axioms bezout04
#print axioms ranges1
#print axioms unit10
#print axioms unit11
#print axioms bezout10
#print axioms bezout11
#print axioms bezout12
#print axioms bezout13
#print axioms bezout14
#print axioms ranges2
#print axioms unit20
#print axioms unit21
#print axioms bezout20
#print axioms bezout21
#print axioms bezout22
#print axioms bezout23
#print axioms bezout24
#print axioms ranges3
#print axioms unit30
#print axioms unit31
#print axioms bezout30
#print axioms bezout31
#print axioms bezout32
#print axioms bezout33
#print axioms bezout34
#print axioms ranges4
#print axioms unit40
#print axioms unit41
#print axioms bezout40
#print axioms bezout41
#print axioms bezout42
#print axioms bezout43
#print axioms bezout44
#print axioms ranges5
#print axioms unit50
#print axioms unit51
#print axioms bezout50
#print axioms bezout51
#print axioms bezout52
#print axioms bezout53
#print axioms bezout54
#print axioms ranges6
#print axioms unit60
#print axioms unit61
#print axioms bezout60
#print axioms bezout61
#print axioms bezout62
#print axioms bezout63
#print axioms bezout64
end RKResearch.Certified.Graded.OrderTwelveFifteen.FourthMaskCore
