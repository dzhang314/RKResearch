module

public import RKCert.ReviewedNative.DyadicBox64
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8TwoZeroLineScalarReceipt

open RKCert.ReviewedNative.DyadicBox64

private def reciprocal (B : Box) : Option Box :=
  if 0 < B.lo ∨ B.hi < 0 then some ⟨B.hi⁻¹,B.lo⁻¹⟩ else none

private theorem reciprocal_sound {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {B D : Box} {x : K} (hx : encloses B x)
    (h : reciprocal B = some D) : encloses D x⁻¹ := by
  unfold reciprocal at h
  split at h
  next hsign =>
    cases h
    simp only [encloses,Rat.cast_inv]
    rcases hsign with hp|hn
    · have lo : 0 < (B.lo : K) := Rat.cast_pos.mpr hp
      have xp : 0 < x := lo.trans_le hx.1
      have hi : 0 < (B.hi : K) := xp.trans_le hx.2
      exact ⟨(inv_le_inv₀ hi xp).2 hx.2,(inv_le_inv₀ xp lo).2 hx.1⟩
    · have hi : (B.hi : K) < 0 := Rat.cast_lt_zero.mpr hn
      have xn : x < 0 := hx.2.trans_lt hi
      have lo : (B.lo : K) < 0 := hx.1.trans_lt xn
      exact ⟨(inv_le_inv_of_neg hi xn).2 hx.2,(inv_le_inv_of_neg xn lo).2 hx.1⟩
  next => contradiction

private def quotient (A B : Box) : Option Box :=
  (reciprocal B).map (mul A)

private theorem quotient_sound {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {A B D : Box} {x y : K}
    (hx : encloses A x) (hy : encloses B y) (h : quotient A B = some D) :
    encloses D (x/y) := by
  cases hB : reciprocal B with
  | none => simp [quotient,hB] at h
  | some R =>
    have e : mul A R = D := by simpa [quotient,hB] using h
    rw [←e,div_eq_mul_inv]
    exact mul_encloses hx (reciprocal_sound hy hB)

/-- The gate is given once, as an arithmetic expression, and evaluated
both over the field and by exact conservative rational interval arithmetic. -/
inductive Expr where
  | left | right | rat : ℚ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr

def fieldValue {K : Type*} [Field K] (a b : K) : Expr → K
  | .left => a
  | .right => b
  | .rat q => q
  | .add u v => fieldValue a b u + fieldValue a b v
  | .sub u v => fieldValue a b u - fieldValue a b v
  | .mul u v => fieldValue a b u * fieldValue a b v
  | .div u v => fieldValue a b u / fieldValue a b v

private def boxValue (A B : Box) : Expr → Option Box
  | .left => some A
  | .right => some B
  | .rat q => some (outward (point q))
  | .add u v => do return add (←boxValue A B u) (←boxValue A B v)
  | .sub u v => do return sub (←boxValue A B u) (←boxValue A B v)
  | .mul u v => do return mul (←boxValue A B u) (←boxValue A B v)
  | .div u v => do quotient (←boxValue A B u) (←boxValue A B v)

section Sound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {x y : K} {A B D : Option Box}

omit [IsStrictOrderedRing K] in
private theorem bind_sound (f : Box → Box → Option Box) {z : K} {T : Box}
    (hx : ∀ U, A=some U → encloses U x) (hy : ∀ U, B=some U → encloses U y)
    (hf : ∀ U V W, f U V=some W → encloses U x → encloses V y → encloses W z)
    (h : (do f (←A) (←B))=some T) : encloses T z := by
  cases A with
  | none => simp at h
  | some U =>
    cases B with
    | none => simp at h
    | some V => exact hf U V T h (hx U rfl) (hy V rfl)

private theorem boxValue_sound {A B : Box} {a b : K}
    (ha : encloses A a) (hb : encloses B b) (e : Expr) :
    ∀ D, boxValue A B e=some D → encloses D (fieldValue a b e) := by
  induction e with
  | left =>
    intro D h
    have he : A=D := by simpa only [boxValue,Option.some.injEq] using h
    rw [←he]
    exact ha
  | right =>
    intro D h
    have he : B=D := by simpa only [boxValue,Option.some.injEq] using h
    rw [←he]
    exact hb
  | rat q =>
    intro D h
    have eq : outward (point q)=D := by simpa [boxValue] using h
    rw [←eq]
    exact outward_encloses (point_encloses q)
  | add u v hu hv =>
    intro D h
    refine bind_sound (fun U V=>some (add U V)) hu hv ?_ h
    intro U V W e hu' hv'
    rw [←Option.some.inj e]
    exact add_encloses hu' hv'
  | sub u v hu hv =>
    intro D h
    refine bind_sound (fun U V=>some (sub U V)) hu hv ?_ h
    intro U V W e hu' hv'
    rw [←Option.some.inj e]
    exact sub_encloses hu' hv'
  | mul u v hu hv =>
    intro D h
    refine bind_sound (fun U V=>some (mul U V)) hu hv ?_ h
    intro U V W e hu' hv'
    rw [←Option.some.inj e]
    exact mul_encloses hu' hv'
  | div u v hu hv =>
    intro D h
    exact bind_sound quotient hu hv (fun _ _ _ e hu' hv'=>quotient_sound hu' hv' e) h

end Sound

local notation "Qₑ" => Expr.rat
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.div

def sqExpr (x : Expr) := x *ₑ x
def cubeExpr (x : Expr) := x *ₑ x *ₑ x

def packet : Expr × Expr × Expr × Expr × Expr :=
  let a := Expr.left
  let b := Expr.right
  let k := a +ₑ b -ₑ Qₑ 2
  let q := (a +ₑ b) *ₑ k -ₑ a *ₑ b +ₑ Qₑ (9/7)
  let r := fun x => sqExpr x +ₑ k *ₑ x +ₑ q
  let J := fun x => x *ₑ (sqExpr x *ₑ Qₑ (1/3) +ₑ k *ₑ x *ₑ Qₑ (1/2) +ₑ q)
  let Jx := fun x => sqExpr x *ₑ (sqExpr x *ₑ Qₑ (1/4) +ₑ k *ₑ x *ₑ Qₑ (1/3) +ₑ q *ₑ Qₑ (1/2))
  let gamma := (J (Qₑ 1) -ₑ J b) /ₑ r b
  (k,q,gamma,J a -ₑ gamma *ₑ r a,Jx a -ₑ gamma *ₑ a *ₑ r a)

/-- The numerator for the silent clock. In the mirror branch the
denominator is zero, so only this expression is tested. -/
def mirrorTest : Expr := packet.2.2.2.2

/-- Gamma, D, d minus gamma, R, R plus gamma squared, and the two
third-row alternatives for each of the three silent-index possibilities.
The formula uses the cleared arithmetic-line gate, with no division by
the neighboring tap or its cubic scalar coefficient. -/
def nonmirrorTests : List Expr :=
  let (k,q,gamma,D,N) := packet
  let r := fun x => sqExpr x +ₑ k *ₑ x +ₑ q
  let d := N /ₑ D
  let R := r gamma
  let B := R +ₑ sqExpr gamma
  let ud := (d -ₑ gamma) /ₑ gamma
  let u := (Qₑ 2 *ₑ R -ₑ gamma *ₑ (Qₑ 2 *ₑ gamma +ₑ k)) /ₑ B
  let kap := fun z => Qₑ 1 +ₑ Qₑ 2 *ₑ z -ₑ sqExpr z
  let star := fun z => R *ₑ kap z -ₑ r (gamma *ₑ (Qₑ 3 -ₑ z))
  let arith := fun z =>
    let w := Qₑ 2 *ₑ z
    let H := Qₑ (-2) +ₑ z +ₑ Qₑ 4 *ₑ sqExpr z -ₑ cubeExpr z
    (R *ₑ kap w -ₑ r (gamma *ₑ (Qₑ 1 +ₑ w))) *ₑ H
      +ₑ Qₑ 4 *ₑ R *ₑ sqExpr z *ₑ (Qₑ 3 *ₑ z -ₑ Qₑ 2)
  [gamma,D,d -ₑ gamma,R,B,star ud,arith ud,ud -ₑ (Qₑ 2 -ₑ u),ud -ₑ Qₑ 2 *ₑ u,
      star u,arith u]

def rootBox (i : Fin 4) : Box :=
  let n : ℚ := (![6943184420297371238,33000947820757186759,
    66999052179242813240,93056815579702628761] : Fin 4 → ℚ) i
  ⟨n / 10^20,(n+1) / 10^20⟩

private def avoidsZero (i j : Fin 4) (e : Expr) : Bool :=
  match boxValue (rootBox i) (rootBox j) e with
  | none => false
  | some B => decide (B.hi < 0 ∨ 0 < B.lo)

private def check (i j : Fin 4) : Bool :=
  if i=j then true
  else if i.val+j.val=3 then avoidsZero i j mirrorTest
  else nonmirrorTests.all (avoidsZero i j)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checks (i j : Fin 4) : check i j=true := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem checked_ne_zero {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b : K} {i j : Fin 4}
    (ha : encloses (rootBox i) a) (hb : encloses (rootBox j) b)
    (e : Expr) (he : avoidsZero i j e=true) : fieldValue a b e≠0 := by
  cases hz : boxValue (rootBox i) (rootBox j) e with
  | none => simp [avoidsZero,hz] at he
  | some B =>
    have h := boxValue_sound ha hb e B hz
    have signs : B.hi < 0 ∨ 0 < B.lo := by simpa [avoidsZero,hz] using he
    rcases signs with s|s
    · exact (sign_neg h s).ne
    · exact (sign_pos h s).ne'

/-- Every one of the eleven guarded expressions for a nonmirror
oriented pair is nonzero on its named two-clock box. -/
theorem nonmirror_checked {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b : K} {i j : Fin 4}
    (ha : encloses (rootBox i) a) (hb : encloses (rootBox j) b)
    (hij : i≠j) (hm : i.val+j.val≠3) :
    ∀ e∈nonmirrorTests, fieldValue a b e≠0 := by
  have h : nonmirrorTests.all (avoidsZero i j)=true := by simpa [check,hij,hm] using checks i j
  intro e he
  exact checked_ne_zero ha hb e (List.all_eq_true.mp h e he)

/-- The mirror-only numerator is nonzero on each of the four directed
mirror boxes; no division by the mirror denominator is made. -/
theorem mirror_checked {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b : K} {i j : Fin 4}
    (ha : encloses (rootBox i) a) (hb : encloses (rootBox j) b)
    (hij : i≠j) (hm : i.val+j.val=3) : fieldValue a b mirrorTest≠0 := by
  apply checked_ne_zero ha hb
  simpa [check,hij,hm] using checks i j

/-- The same two-stage gates on actual field scalars, independent of
the expression datatype or the interval checker. -/
def scalarTests {K : Type*} [Field K] (a b : K) : List K :=
  let k := a+b-2
  let q := (a+b)*k-a*b+9/7
  let r := fun x : K => x*x+k*x+q
  let J := fun x : K => x*(x*x*(1/3)+k*x*(1/2)+q)
  let Jx := fun x : K => (x*x)*((x*x)*(1/4)+k*x*(1/3)+q*(1/2))
  let gamma := (J 1-J b)/r b
  let D := J a-gamma*r a
  let N := Jx a-gamma*a*r a
  let d := N/D
  let R := r gamma
  let B := R+gamma*gamma
  let ud := (d-gamma)/gamma
  let u := (2*R-gamma*(2*gamma+k))/B
  let kap := fun z : K => 1+2*z-z*z
  let S := fun z : K => R*kap z-r (gamma*(3-z))
  let T := fun z : K =>
    let w := 2*z
    let H := -2+z+4*(z*z)-z*z*z
    (R*kap w-r (gamma*(1+w)))*H + 4*R*(z*z)*(3*z-2)
  [gamma,D,d-gamma,R,B,S ud,T ud,ud-(2-u),ud-2*u,S u,T u]

/-- The only scalar checked in the mirror orientation. -/
def scalarMirrorNumerator {K : Type*} [Field K] (a b : K) : K :=
  let k := a+b-2
  let q := (a+b)*k-a*b+9/7
  let r := fun x : K => x*x+k*x+q
  let J := fun x : K => x*(x*x*(1/3)+k*x*(1/2)+q)
  let Jx := fun x : K => (x*x)*((x*x)*(1/4)+k*x*(1/3)+q*(1/2))
  let gamma := (J 1-J b)/r b
  Jx a-gamma*a*r a

section Binding

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem map_nonmirrorTests (a b : K) :
    nonmirrorTests.map (fieldValue a b) = scalarTests a b := by
  simp [nonmirrorTests,packet,fieldValue,scalarTests,sqExpr,cubeExpr,Rat.cast_div,Rat.cast_neg]

theorem map_mirrorTest (a b : K) : fieldValue a b mirrorTest = scalarMirrorNumerator a b := by
  simp [mirrorTest,packet,fieldValue,scalarMirrorNumerator,sqExpr,Rat.cast_div]

theorem scalar_nonmirror_nonzero {a b : K} {i j : Fin 4}
    (ha : encloses (rootBox i) a) (hb : encloses (rootBox j) b)
    (hij : i≠j) (hm : i.val+j.val≠3) :
    ∀ x∈scalarTests a b, x≠0 := by
  rw [←map_nonmirrorTests a b]
  intro x h
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
  exact nonmirror_checked ha hb hij hm e he

theorem scalar_mirror_nonzero {a b : K} {i j : Fin 4}
    (ha : encloses (rootBox i) a) (hb : encloses (rootBox j) b)
    (hij : i≠j) (hm : i.val+j.val=3) : scalarMirrorNumerator a b≠0 := by
  rw [←map_mirrorTest a b]
  exact mirror_checked ha hb hij hm

end Binding

def quartic70 (x : ℚ) := ((70*x-140)*x+90)*x*x-20*x+1

/-- Signs of the actual shifted Legendre polynomial at the four
rational bracket endpoints, with the positive normalization 70. -/
theorem rootBox_opposite_signs (i : Fin 4) :
    quartic70 (rootBox i).lo * quartic70 (rootBox i).hi < 0 := by
  fin_cases i <;> decide +kernel

end RKCert.ReviewedNative.SDIRK8TwoZeroLineScalarReceipt
