module

public import RKCert.ReviewedNative.HankelLegendreIntData

@[expose] public section

/-! # Division-cleared certificates for the literal Legendre rows

An expression denotes a polynomial, but the checks reduce only
integer coefficient convolutions, never a field polynomial or a
sampled field. A bound on degree records the exact checked range. -/
namespace RKResearch.Certified.Graded.HankelLegendreScalarData

open HankelLegendreIntData

abbrev RowBand (r : ScaledRow) (n : ℕ) : Prop :=
  r.denominator ∣ paidNat^2 ∧ r.numerator.length = n+1 ∧
  coeffInt r n = (r.denominator : ℤ) ∧
  ∀ i : Fin (n+1), i.val%2 ≠ n%2 → coeffInt r i.val = 0

set_option maxRecDepth 4096 in
theorem tail_bands :
    (∀ n : Fin 7, RowBand (tailRow 5 n.val) n.val) ∧
    (∀ n : Fin 6, RowBand (tailRow 6 n.val) n.val) ∧
    (∀ n : Fin 5, RowBand (tailRow 7 n.val) n.val) := by
  decide +kernel

inductive Expr where
  | row : ScaledRow → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

def Expr.denom : Expr → ℕ
  | .row r => r.denominator
  | .add a b | .sub a b | .mul a b => a.denom*b.denom

def Expr.height : Expr → ℕ
  | .row r => r.numerator.length-1
  | .add a b | .sub a b => Nat.max a.height b.height
  | .mul a b => a.height+b.height

def convPrefix (a b : ℕ → ℤ) (j : ℕ) : ℕ → ℤ
  | 0 => 0
  | k+1 => convPrefix a b j k + a k * b (j-k)

def Expr.numCoeff : Expr → ℕ → ℤ
  | .row r,j => coeffInt r j
  | .add a b,j => a.numCoeff j * (b.denom : ℤ) + (a.denom : ℤ)*b.numCoeff j
  | .sub a b,j => a.numCoeff j * (b.denom : ℤ) - (a.denom : ℤ)*b.numCoeff j
  | .mul a b,j => convPrefix a.numCoeff b.numCoeff j (j+1)

structure ZeroData (e : Expr) : Prop where
  denomPaid : e.denom ∣ paidNat^16
  zero : ∀ j : Fin (e.height+1), e.numCoeff j.val = 0

structure CoeffData (e : Expr) (j : ℕ) (num : ℤ) (den : ℕ) : Prop where
  denomPaid : e.denom ∣ paidNat^16
  denPaid : den ∣ paidNat^2
  cleared : e.numCoeff j * (den : ℤ) = num*(e.denom : ℤ)

def eX : Expr := .row ⟨1,[0,1]⟩
def eMode (n : ℕ) : Expr := .row (modeRow n)
def eTail (a n : ℕ) : Expr := .row (tailRow a n)
def eRat (num : ℤ) (den : ℕ) : Expr := .row ⟨den,[num]⟩
def eBeta (n : ℕ) : Expr := eRat ((n*n : ℕ) : ℤ) ((2*n-1)*(2*n+1))

local infixl:65 " ⊞ " => Expr.add
local infixl:65 " ⊟ " => Expr.sub
local infixl:70 " ⊠ " => Expr.mul

def modeRec (n : ℕ) : Expr :=
  eMode (n+1) ⊟ (eX ⊠ eMode n ⊟ eBeta n ⊠ eMode (n-1))

def continuation (n a : ℕ) : Expr :=
  eMode n ⊟ (eTail (a+1) (n-a) ⊠ eMode a ⊟ eBeta a ⊠ eTail (a+2) (n-a-1) ⊠ eMode (a-1))

def tailStep74 : Expr := eTail 7 4 ⊟ (eX ⊠ eTail 7 3 ⊟ eBeta 9 ⊠ eTail 7 2)

def eCoeff55 : Expr := eTail 6 4 ⊟ eMode 4
def eCoeff45 : Expr := eTail 5 4 ⊟ eMode 4
def eCubicI : Expr := eX ⊠ eTail 6 4 ⊟ eMode 5
def eOddI : Expr := eX ⊠ eTail 6 4 ⊟ eRat 601 1683 ⊠ eTail 7 3 ⊟ eMode 5
def eEvenI : Expr :=
  (eRat 601 1683 ⊞ eBeta 5) ⊠ (eX ⊠ eTail 7 3) ⊟ eRat 601 1683 ⊠ eTail 6 4 ⊟ eBeta 5 ⊠ eMode 4
def eTwoII : Expr := eMode 5 ⊟ eX ⊠ eTail 7 4
def eCubicIII : Expr := eX ⊠ eMode 4 ⊟ eTail 5 5
def eLinearIII : Expr := eX ⊠ eMode 4 ⊟ eRat 160 1071 ⊠ eMode 3 ⊟ eTail 5 5
def eCubicIV : Expr := eTail 6 5 ⊟ eX ⊠ eMode 4

set_option maxRecDepth 4096

theorem rec1 : ZeroData (modeRec 1) := ⟨by decide +kernel, by decide +kernel⟩
theorem rec2 : ZeroData (modeRec 2) := ⟨by decide +kernel, by decide +kernel⟩
theorem rec3 : ZeroData (modeRec 3) := ⟨by decide +kernel, by decide +kernel⟩
theorem rec4 : ZeroData (modeRec 4) := ⟨by decide +kernel, by decide +kernel⟩

theorem cont84 : ZeroData (continuation 8 4) := ⟨by decide +kernel, by decide +kernel⟩
theorem cont94 : ZeroData (continuation 9 4) := ⟨by decide +kernel, by decide +kernel⟩
theorem cont104 : ZeroData (continuation 10 4) := ⟨by decide +kernel, by decide +kernel⟩
theorem cont95 : ZeroData (continuation 9 5) := ⟨by decide +kernel, by decide +kernel⟩
theorem cont105 : ZeroData (continuation 10 5) := ⟨by decide +kernel, by decide +kernel⟩
theorem tail74 : ZeroData tailStep74 := ⟨by decide +kernel, by decide +kernel⟩

theorem c55 : CoeffData eCoeff55 2 135 1309 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem c45 : CoeffData eCoeff45 2 32 315 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem cI : CoeffData eCubicI 3 601 1683 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem lI : CoeffData eOddI 1 6432 1446445 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem eI : CoeffData eEvenI 2 33603 187187 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem cII : CoeffData eTwoII 3 (-796) 2223 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem lII : CoeffData eTwoII 1 77192 440895 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem cIII : CoeffData eCubicIII 3 160 1071 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem lIII : CoeffData eLinearIII 1 (-96) 6545 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem cIV : CoeffData eCubicIV 3 (-216) 1463 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end RKResearch.Certified.Graded.HankelLegendreScalarData
