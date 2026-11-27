import Lean

/-! Boundary-polynomial receipts and the paid mixed-root induction.
The original context operations and weighted adjoint are supplied
by the actual old/live tableau bridge. -/
namespace RKResearch.ERK10ZeroInjectiveF4Gate
inductive Word where
| unit : Word
| advance : Word → Word
| mul : Word → Word → Word

def grade : Word → Nat
| .unit => 0
| .advance t => grade t+1
| .mul t u => grade t+grade u

structure Semantics (V : Type) where
  unitValue : V
  advanceValue : V → V
  productValue : V → V → V

def eval {V : Type} (S : Semantics V) : Word → V
| .unit => S.unitValue
| .advance t => S.advanceValue (eval S t)
| .mul t u => S.productValue (eval S t) (eval S u)

structure MixedPairing (V P Z K : Type) (num : Semantics V) (model : Semantics P) where
  ctxGrade : Z → Nat
  zeroAtOrigin : Z → Prop
  nextCtx : Z → Z
  mulCtx : Word → Z → Z
  actual : V → Z → K
  scalar : P → Z → K
  nextPaid : ∀ z, ctxGrade (nextCtx z) ≤ ctxGrade z+1
  mulPaid : ∀ t z, ctxGrade (mulCtx t z) ≤ ctxGrade z+grade t
  nextZero : ∀ z, zeroAtOrigin z → zeroAtOrigin (nextCtx z)
  mulZero : ∀ t z, grade t≤4 → zeroAtOrigin z → zeroAtOrigin (mulCtx t z)
  base : ∀ z, ctxGrade z≤9 → zeroAtOrigin z →
    actual num.unitValue z=scalar model.unitValue z
  adjointActual : ∀ v z, zeroAtOrigin z →
    actual (num.advanceValue v) z=actual v (nextCtx z)
  adjointScalar : ∀ p z, scalar (model.advanceValue p) z=scalar p (nextCtx z)
  mulActualLeft : ∀ t v z, grade t≤4 →
    actual (num.productValue (eval num t) v) z=actual v (mulCtx t z)
  mulScalarLeft : ∀ t p z, grade t≤4 →
    scalar (model.productValue (eval model t) p) z=scalar p (mulCtx t z)
  mulActualRight : ∀ t v z, grade t≤4 →
    actual (num.productValue v (eval num t)) z=actual v (mulCtx t z)
  mulScalarRight : ∀ t p z, grade t≤4 →
    scalar (model.productValue p (eval model t)) z=scalar p (mulCtx t z)

theorem mixedRoot {V P Z K : Type} {num : Semantics V} {model : Semantics P}
    (h : MixedPairing V P Z K num model) (t : Word) :
    ∀ z, h.zeroAtOrigin z → h.ctxGrade z+grade t≤9 →
        h.actual (eval num t) z=h.scalar (eval model t) z := by
  induction t with
  | unit =>
    intro z hz pay
    exact h.base z (by simpa [grade] using pay) hz
  | advance t ih =>
    intro z hz pay
    have pay' := h.nextPaid z
    simp only [eval, h.adjointActual _ _ hz, h.adjointScalar]
    have hp : h.ctxGrade z+(grade t+1)≤9 := pay
    exact ih (h.nextCtx z) (h.nextZero z hz) (by omega)
  | mul t u it iu =>
    intro z hz pay
    have hp : h.ctxGrade z+(grade t+grade u)≤9 := pay
    by_cases ht : grade t≤4
    · have pay' := h.mulPaid t z
      simp only [eval, h.mulActualLeft _ _ _ ht, h.mulScalarLeft _ _ _ ht]
      exact iu (h.mulCtx t z) (h.mulZero t z ht hz) (by omega)
    · have hu : grade u≤4 := by omega
      have pay' := h.mulPaid u z
      simp only [eval, h.mulActualRight _ _ _ hu, h.mulScalarRight _ _ _ hu]
      exact it (h.mulCtx u z) (h.mulZero u z hu hz) (by omega)

theorem weightedSizeNine {V P Z K : Type} {num : Semantics V} {model : Semantics P}
    (h : MixedPairing V P Z K num model) (clock : Z)
    (zero : h.zeroAtOrigin clock) (one : h.ctxGrade clock=1)
    (t : Word) (g : grade t≤8) :
    h.actual (eval num t) clock=h.scalar (eval model t) clock :=
  mixedRoot h t clock zero (by omega)

def legendre : List Int := [1,-30,210,-560,630,-252]
def lobattoAlias : List Int := [1,-15,70,-140,126,-42]
def moment2520 (a : List Int) (j : Nat) : Int :=
  a.zipIdx.foldl (fun s (v,i) => s+v*(2520/(i+j+1):Int)) 0

theorem legendreMoment : ∀ j : Fin 5, moment2520 legendre j.val=0 := by decide
theorem legendreTerminal : legendre.foldl (·+·) 0=(-1:Int) := by decide
theorem aliasMoment : ∀ j : Fin 4, moment2520 lobattoAlias (j.val+1)=0 := by decide
theorem aliasMean : moment2520 lobattoAlias 0=84 := by decide

end RKResearch.ERK10ZeroInjectiveF4Gate
#print axioms RKResearch.ERK10ZeroInjectiveF4Gate.mixedRoot
#print axioms RKResearch.ERK10ZeroInjectiveF4Gate.weightedSizeNine
#print axioms RKResearch.ERK10ZeroInjectiveF4Gate.legendreMoment
#print axioms RKResearch.ERK10ZeroInjectiveF4Gate.legendreTerminal
#print axioms RKResearch.ERK10ZeroInjectiveF4Gate.aliasMoment
#print axioms RKResearch.ERK10ZeroInjectiveF4Gate.aliasMean
