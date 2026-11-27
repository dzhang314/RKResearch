import Lean

/-!
# Local algebraic gates for the ordinary order-eleven sharp-prefix branch

This file is independent of mathlib. It checks the consecutive weighted
first-seed obstruction, the second-seed obstruction, and the graded
substitution used in physical row deletion. The separate paper proves
the actual rank, exactness and rooted-space premises for RK tableaux.
-/
namespace RKResearch.ERK11PureTailGate
open Lean.Grind

section Rows
variable {K : Type} [Field K]
abbrev Vec (K : Type) (n : Nat) := Fin n → K

def Last {n : Nat} (r : Vec K n) (j : Fin n) : Prop :=
  r j ≠ 0 ∧ ∀ i : Fin n, j < i → r i = 0

def DropsLast {n : Nat} (rightA : Vec K n → Vec K n) : Prop :=
  ∀ r j, Last r j → rightA r j = 0

def clockMul {n : Nat} (r y : Vec K n) : Vec K n := fun i => r i * y i

/-- Two consecutive normalized outputs with both first reverse seeds
zero cannot occupy one strict explicit tableau. -/
theorem noConsecutiveFirstSeeds {n : Nat}
    (y r0 r1 : Vec K n) (rightA : Vec K n → Vec K n)
    (strict : DropsLast rightA) (j : Fin n) (live : Last r1 j)
    (m0 m1 : K) (paid : m0 ≠ 0)
    (transfer : rightA r0 = r1)
    (first : ∀ i, m0 * rightA r0 i = r0 i * y i)
    (next : ∀ i, m1 * rightA r1 i = r1 i * y i) : False := by
  have ex := next j
  rw [strict r1 j live, Semiring.mul_zero] at ex
  have y0 := (Field.of_mul_eq_zero ex.symm).resolve_left live.1
  have e := first j
  rw [transfer,y0,Semiring.mul_zero] at e
  exact live.1 ((Field.of_mul_eq_zero e).resolve_left paid)

/-- The second seed cannot vanish if the row has a nonzero positive
clock-weighted read. Use its last actual nonzero r*y coordinate. -/
theorem noZeroSecondSeed {n : Nat}
    (r y : Vec K n) (rightA : Vec K n → Vec K n)
    (strict : DropsLast rightA) (m : K) (j : Fin n)
    (live : Last (clockMul r y) j)
    (second : ∀ i, m * rightA (clockMul r y) i = (clockMul r y) i * y i) : False := by
  have z := second j
  rw [strict (clockMul r y) j live, Semiring.mul_zero] at z
  have y0 := (Field.of_mul_eq_zero z.symm).resolve_left live.1
  apply live.1
  simp [clockMul,y0,Semiring.mul_zero]

def coord {n : Nat} (i : Fin n) : Vec K n :=
  fun j => if j = i then 1 else 0

/-- A vanishing tested row must vanish coefficientwise if its test
subspace contains all actual coordinate vectors. -/
theorem fullTestsKillRow {n : Nat} (eval : Vec K n → Vec K n → K)
    (space : Vec K n → Prop) (r : Vec K n)
    (coordinate : ∀ i, eval r (coord i) = r i)
    (full : ∀ i, space (coord i))
    (vanishes : ∀ v, space v → eval r v = 0) : r = fun _ => 0 := by
  funext i
  rw [← coordinate i]
  exact vanishes _ (full i)
end Rows

section Delete
variable {K : Type} [Field K]

/-- Replace just one physical read by a linear read of earlier sites.
The paper uses this for an actual causal row and a pure defect coordinate. -/
def replace {n : Nat} (pivot : Fin n)
    (previous : Vec K n → K) (v : Vec K n) : Vec K n :=
  fun j => if j = pivot then previous v else v j

theorem replaceEq {n : Nat} (pivot : Fin n) (previous : Vec K n → K)
    (v : Vec K n) :
    replace pivot previous v =
      fun j => v j + (previous v - v pivot) * coord pivot j := by
  funext j
  by_cases h : j = pivot
  · subst j
    simp [replace,coord]
    grind
  · simp [replace,coord,h,Semiring.mul_zero,Semiring.add_zero]

omit [Field K] in
theorem replaceUnchanged {n : Nat} (pivot : Fin n) (previous : Vec K n → K)
    (v : Vec K n) (h : previous v = v pivot) : replace pivot previous v = v := by
  funext j
  by_cases e : j = pivot
  · subst j
    simp [replace,h]
  · simp [replace,e]

def Causal {n : Nat} (leftA : Vec K n → Vec K n) : Prop :=
  ∀ (j : Fin n) x y, (∀ k : Fin n, k < j → x k = y k) → leftA x j = leftA y j

def Earlier {n : Nat} (pivot : Fin n) (previous : Vec K n → K) : Prop :=
  ∀ x y, (∀ k : Fin n, k < pivot → x k = y k) → previous x = previous y

omit [Field K] in
/-- The rewritten square matrix is still strict in literal chronology. -/
theorem replaceCausal {n : Nat} (pivot : Fin n) (previous : Vec K n → K)
    (leftA : Vec K n → Vec K n) (a : Causal leftA) (h : Earlier pivot previous) :
    Causal (fun v => leftA (replace pivot previous v)) := by
  intro j x y eq
  apply a j
  intro k hk
  by_cases e : k = pivot
  · subst k
    simp only [replace]
    exact h x y (fun k s => eq k (Fin.lt_trans s hk))
  · simp only [replace,ite_eq_right e]
    exact eq k hk

omit [Field K] in
/-- The rewritten numerical action and output cannot see the deleted
coordinate, including on arbitrary inputs. -/
theorem replaceIgnoresPivot {n : Nat} (pivot : Fin n)
    (previous : Vec K n → K) (h : Earlier pivot previous)
    (x y : Vec K n) (off : ∀ j : Fin n, j ≠ pivot → x j = y j) :
    replace pivot previous x = replace pivot previous y := by
  have e := h x y (fun _ lt => off _ (Fin.ne_of_lt lt))
  funext j
  by_cases p : j = pivot
  · subst j
    simp [replace,e]
  · simp [replace,p,off _ p]

/-- A rooted pair relation can absorb the coordinate replacement if
low-grade inputs already satisfy it, and if high-grade pairs can add
any scalar multiple of the pure pivot. -/
theorem gradedReplace {n : Nat} {M : Type}
    (pair : Nat → Vec K n → M → Prop)
    (pivot : Fin n) (previous : Vec K n → K) (enter : Nat)
    (early : ∀ j v p, j < enter → pair j v p → previous v = v pivot)
    (pure : ∀ j v p (a : K), enter ≤ j → pair j v p →
      pair j (fun i => v i + a * coord pivot i) p)
    {j : Nat} {v : Vec K n} {p : M} (h : pair j v p) :
    pair j (replace pivot previous v) p := by
  by_cases le : enter ≤ j
  · rw [replaceEq]
    exact pure j v p _ le h
  · have e := early j v p (Nat.lt_of_not_ge le) h
    rw [replaceUnchanged pivot previous v e]
    exact h

/-- Chronological representative of a quotient by a pure clock line,
normalized to value one at its first supporting coordinate. -/
def eraseAlong {n : Nat} (p : Fin n) (v x : Vec K n) : Vec K n :=
  fun j => x j - x p * v j

theorem eraseAtPivot {n : Nat} (p : Fin n) (v x : Vec K n) (hp : v p=1) :
    eraseAlong p v x p = 0 := by
  rw [eraseAlong,hp,Semiring.mul_one,AddCommGroup.sub_self]

/-- Reprojecting a strict action along a vector whose physical support
starts at the pivot preserves strict chronology. No pointwise product
on the quotient is asserted. -/
theorem eraseCausal {n : Nat} (p : Fin n) (v : Vec K n) (hp : v p=1)
    (start : ∀ i, i < p → v i=0)
    (leftA : Vec K n → Vec K n) (strict : Causal leftA) :
    Causal (fun x => eraseAlong p v (leftA x)) := by
  intro j x y eq
  change eraseAlong p v (leftA x) j = eraseAlong p v (leftA y) j
  have w := strict j x y eq
  by_cases h : j=p
  · subst j
    rw [eraseAtPivot p v _ hp,eraseAtPivot p v _ hp]
  · by_cases b : p<j
    · have e := strict p x y (fun k q => eq k (Fin.lt_trans q b))
      simp only [eraseAlong,w,e]
    · have rt : j<p := by omega
      simp only [eraseAlong,start j rt,Semiring.mul_zero,w]

/-- Clock multiplication commutes with this representative when the
pure line is an actual one-clock eigenvector. -/
theorem eraseClock {n : Nat} (p : Fin n) (v y x : Vec K n)
    (localClock : ∀ j, y j*v j=y p*v j) :
    eraseAlong p v (clockMul x y) = clockMul (eraseAlong p v x) y := by
  funext j
  simp only [eraseAlong,clockMul]
  have e := congrArg (fun w => x p*w) (localClock j)
  grind

/-- The top-visible five-site equations cannot have a nonzero second
response with zero third response and unequal adjacent clocks. -/
theorem middleZero (y0 y1 y3 y4 V : K)
    (adj0 : y0≠y1) (adj3 : y3≠y4)
    (h03 : y0*(y3*V)=0) (h04 : y0*(y4*V)=0)
    (h13 : y1*(y3*V)=0) (h14 : y1*(y4*V)=0) : V=0 := by
  by_cases nv : V=0
  · exact nv
  · exfalso
    by_cases hy : y0=0
    · have nz : y1≠0 := fun q => adj0 (hy.trans q.symm)
      have a := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero h13).resolve_left nz)).resolve_right nv
      have b := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero h14).resolve_left nz)).resolve_right nv
      exact adj3 (a.trans b.symm)
    · have a := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero h03).resolve_left hy)).resolve_right nv
      have b := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero h04).resolve_left hy)).resolve_right nv
      exact adj3 (a.trans b.symm)
end Delete

/-- Binary syntax sufficient for all rooted extensions and root products.
A product merges roots; its grade is the sum of the two grades. -/
inductive Profile
  | leaf
  | unary (t : Profile)
  | join (t s : Profile)

def grade : Profile → Nat
  | .leaf => 0
  | .unary t => grade t + 1
  | .join t s => grade t + grade s

def compute {X : Type} (one : X) (a : X → X) (prod : X → X → X) : Profile → X
  | .leaf => one
  | .unary t => a (compute one a prod t)
  | .join t s => prod (compute one a prod t) (compute one a prod s)

/-- The augmented exact computation applies the paid model-preserving
projection on the input of each primitive and once at output.
This induction also handles every mixed-root product. -/
theorem projectedRootExact {V M O : Type}
    (pair : Nat → V → M → Prop) (one : V) (modelOne : M)
    (a : V → V) (j : M → M) (prod : V → V → V) (modelProd : M → M → M)
    (project : V → V) (view : V → O) (expected : M → O) (budget : Nat)
    (leaf : pair 0 one modelOne)
    (unary : ∀ g x p, pair g x p → pair (g+1) (a x) (j p))
    (joined : ∀ g h x y p q, pair g x p → pair h y q →
      pair (g+h) (prod x y) (modelProd p q))
    (projectGood : ∀ g x p, g ≤ budget → pair g x p → pair g (project x) p)
    (exactOut : ∀ g x p, g ≤ budget → pair g x p → view x = expected p)
    (t : Profile) (paid : grade t ≤ budget) :
    view (project (compute one (fun x => a (project x)) prod t)) =
       expected (compute modelOne j modelProd t) := by
  have inner : ∀ t, grade t ≤ budget →
      pair (grade t) (compute one (fun x => a (project x)) prod t)
        (compute modelOne j modelProd t) := by
    intro s
    induction s with
    | leaf =>
      intro _
      exact leaf
    | unary t ih =>
      intro h
      have q : grade t ≤ budget := Nat.le_trans (Nat.le_succ _) h
      exact unary _ _ _ (projectGood _ _ _ q (ih q))
    | join t s ht hs =>
      intro h
      exact joined _ _ _ _ _ _ (ht (Nat.le_trans (Nat.le_add_right _ _) h))
        (hs (Nat.le_trans (Nat.le_add_left _ _) h))
  exact exactOut _ _ _ paid (projectGood _ _ _ paid (inner _ paid))



section CustomSeed
variable {K : Type} [Field K]

/-- The exact denominator-cleared scalar identity used for the non-Beta
custom prefix weight and its upper primitive. -/
theorem customSeedPolynomial (y x : K) :
    (2*x-y)*(x^2*(x-y)^2)=x*(x-y)*(x*(x-y)*(2*x-y)) := by
  grind

/-- If an input projection fixes every paid child, the new numerical
stage vectors at the next grade already agree exactly. No pure
coordinate is needed in this special-case deletion. -/
theorem lowerAgreement {V : Type} (one : V) (a : V → V)
    (prod : V → V → V) (project : V → V) (budget : Nat)
    (fixChild : ∀ t, grade t+1 ≤ budget →
        project (compute one a prod t)=compute one a prod t)
    (t : Profile) (paid : grade t≤budget) :
    compute one (fun x => a (project x)) prod t=compute one a prod t := by
  induction t with
  | leaf => rfl
  | unary t h =>
    have q : grade t≤budget := Nat.le_trans (Nat.le_succ _) paid
    change a (project (compute one (fun x => a (project x)) prod t)) =
      a (compute one a prod t)
    rw [h q,fixChild t paid]
  | join t s ht hs =>
    change prod (compute one (fun x => a (project x)) prod t)
        (compute one (fun x => a (project x)) prod s) = _
    rw [ht (Nat.le_trans (Nat.le_add_right _ _) paid),
      hs (Nat.le_trans (Nat.le_add_left _ _) paid)]
    rfl
end CustomSeed

section LocalExample
/-! The ordinary (not previously weighted-shift-two) five-slot data
actually satisfy every budget-four word and the full first-seed row
identity. They do not claim a rooted order-eleven tableau. -/
structure RatFive where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat

def modelA (v : RatFive) : RatFive :=
  ⟨0,v.a,v.a/2+v.b,-v.b/2+v.c,v.a/16+v.b/4+v.d⟩
def modelY (v : RatFive) : RatFive := ⟨4*v.a,4*v.b,2*v.c,v.d,0⟩
def modelB (v : RatFive) : Rat := 3*v.a/32+v.b/16+v.c/2+v.d+v.e

inductive Op | A | Y

def words : List Op → RatFive
  | [] => ⟨1,0,0,0,0⟩
  | .A::xs => modelA (words xs)
  | .Y::xs => modelY (words xs)

def factor (j : Nat) : List Op → Rat
  | [] => 1
  | .A::xs => factor (j+1) xs
  | .Y::xs => (j:Rat)*factor (j+1) xs

def modelMoments : Nat → Rat
  | 0 => 3/32
  | 1 => 3/8
  | 2 => 3/4
  | 3 => 1
  | _ => 1

theorem localAllWords (w : List Op) (paid : w.length≤4) :
    modelB (words w) = factor 1 w * modelMoments w.length := by
  match w with
  | [] => decide +kernel
  | [a] => cases a <;> decide +kernel
  | [a,b] => cases a <;> cases b <;> decide +kernel
  | [a,b,c] => cases a <;> cases b <;> cases c <;> decide +kernel
  | [a,b,c,d] => cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel
  | _::_::_::_::_::xs => simp only [List.length_cons] at paid; omega

theorem localPositiveTaps :
    modelB (words [.A,.A,.A]) = 1 ∧ modelB (words [.A,.A,.A,.A]) = 1 := by
  decide +kernel

def ratCoord5 (i : Fin 5) : RatFive :=
  ⟨if i=0 then 1 else 0, if i=1 then 1 else 0, if i=2 then 1 else 0,
    if i=3 then 1 else 0, if i=4 then 1 else 0⟩

theorem localFirstSeed : ∀ i : Fin 5,
    modelB (modelA (ratCoord5 i)) = modelB (modelY (ratCoord5 i)) := by
  decide +kernel
end LocalExample

end RKResearch.ERK11PureTailGate
#print axioms RKResearch.ERK11PureTailGate.noConsecutiveFirstSeeds
#print axioms RKResearch.ERK11PureTailGate.noZeroSecondSeed
#print axioms RKResearch.ERK11PureTailGate.fullTestsKillRow
#print axioms RKResearch.ERK11PureTailGate.replaceCausal
#print axioms RKResearch.ERK11PureTailGate.replaceIgnoresPivot
#print axioms RKResearch.ERK11PureTailGate.gradedReplace
#print axioms RKResearch.ERK11PureTailGate.projectedRootExact

#print axioms RKResearch.ERK11PureTailGate.eraseCausal
#print axioms RKResearch.ERK11PureTailGate.eraseClock
#print axioms RKResearch.ERK11PureTailGate.middleZero
#print axioms RKResearch.ERK11PureTailGate.localAllWords
#print axioms RKResearch.ERK11PureTailGate.localPositiveTaps

#print axioms RKResearch.ERK11PureTailGate.localFirstSeed
#print axioms RKResearch.ERK11PureTailGate.customSeedPolynomial
#print axioms RKResearch.ERK11PureTailGate.lowerAgreement
