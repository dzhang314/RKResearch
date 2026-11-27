import Lean

/-! Scalar late-clock contradiction and rooted signed-pair quotient. -/
namespace RKResearch.ERK10SingleGhostLatePairGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] {s : Nat}

def lobatto (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def scaledAtRatio (x : K) : K := 3402*x^4-4536*x^3+2016*x^2-336*x+16
theorem transformRatio (x : K) :
    16*lobatto ((3/2:K)*x)=scaledAtRatio x := by
  unfold lobatto scaledAtRatio
  by_cases hh : (2:K)=0
  · have zz : (16:K)=0 := by grind
    grind
  · grind
theorem clockBezout (x : K) :
    (-12308436*x^3+13451508*x^2-3902094*x+273591)*lobatto x+
    (151956*x^3-267372*x^2+136374*x-16519)*scaledAtRatio x=9287 := by
  unfold lobatto scaledAtRatio
  grind
theorem noLobattoRatio [IsCharP K 0] (x : K)
    (first : lobatto x=0) (second : lobatto ((3/2:K)*x)=0) : False := by
  have ds := transformRatio x
  have bz := clockBezout x
  grind

/-- A literal clean reverse row cannot have a new nonzero clock if
the only preceding nonzero clock is w and all three primitives are paid. -/
theorem onlyOrigin [IsCharP K 0] (a w y : K) (hw : w ≠ 0)
    (m1 : 2*a*w=y^2) (m2 : 3*a*w^2=y^3) (m3 : 4*a*w^3=y^4) :
    y=0 := by
  by_cases hy : y=0
  · exact hy
  · have cross1 : y^2*(2*y-3*w)=0 := by grind
    have cross2 : y^3*(3*y-4*w)=0 := by grind
    have lin1 : 2*y-3*w=0 := by grind
    have lin2 : 3*y-4*w=0 := by grind
    grind

variable (a g h : Fin s)

def quotient (x : (Fin s → K)) : (Fin s → K) :=
  fun i => if i=g then 0 else if i=h then x a+x h-x g else x i
def sectionMap (x : (Fin s → K)) : (Fin s → K) :=
  fun i => if i=g then 0 else if i=h then x h-x a else x i
def cancelled (x : (Fin s → K)) : (Fin s → K) :=
  fun i => if i=g ∨ i=h then x i-x g else x i
def prod (x y : (Fin s → K)) : (Fin s → K) := fun i => x i*y i
def oldUnit : (Fin s → K) := fun _ => 1

theorem sectionQuotient (ag : a ≠ g) (ah : a ≠ h) (gh : g ≠ h)
    (x : (Fin s → K)) :
    sectionMap a g h (quotient a g h x)=cancelled g h x := by
  funext i
  by_cases ig : i=g
  · subst i
    simp [sectionMap,cancelled] <;> grind
  · by_cases ih : i=h
    · subst i
      simp [sectionMap,quotient,cancelled,Ne.symm gh,ag,ah] <;> grind
    · simp [sectionMap,quotient,cancelled,ig,ih]

/-- Equal on the late pair suffices if both factors are equal there.
If just one factor is equal there, its value must also match the
retained, earlier anchor. -/
theorem quotientProd (gh : g ≠ h) (x y : (Fin s → K))
    (support : (x g=x h ∧ y g=y h) ∨
      (x a=x g ∧ x g=x h) ∨ (y a=y g ∧ y g=y h)) :
    quotient a g h (prod x y)=prod (quotient a g h x) (quotient a g h y) := by
  funext i
  by_cases ig : i=g
  · subst i
    simp [quotient,prod] <;> grind
  · by_cases ih : i=h
    · subst i
      simp [quotient,prod,Ne.symm gh]
      rcases support with hs | hs | hs <;> grind
    · simp [quotient,prod,ig,ih]

def Strict (A : (Fin s → K) → (Fin s → K)) : Prop :=
  ∀ i x y, (∀ j : Fin s, j.val<i.val → x j=y j) → A x i=A y i
def Causal (A : (Fin s → K) → (Fin s → K)) : Prop :=
  ∀ i x y, (∀ j : Fin s, j.val≤i.val → x j=y j) → A x i=A y i

theorem quotientCausal (ax : a.val<h.val) (gx : g.val<h.val) :
    Causal (quotient (K:=K) a g h) := by
  intro i x y he
  by_cases ig : i=g
  · simp [quotient,ig]
  · by_cases ih : i=h
    · subst i
      simp [quotient,ig,he a (by omega),he h (by omega),he g (by omega)]
    · simp [quotient,ig,ih,he i (by omega)]

theorem sectionCausal (ax : a.val<h.val) : Causal (sectionMap (K:=K) a g h) := by
  intro i x y he
  by_cases ig : i=g
  · simp [sectionMap,ig]
  · by_cases ih : i=h
    · subst i
      simp [sectionMap,ig,he a (by omega),he h (by omega)]
    · simp [sectionMap,ig,ih,he i (by omega)]

def reducedA (A : (Fin s → K) → (Fin s → K)) : (Fin s → K) → (Fin s → K) :=
  fun x => quotient a g h (A (sectionMap a g h x))

theorem strictReduced (ax : a.val<h.val) (gx : g.val<h.val)
    (A : (Fin s → K) → (Fin s → K)) (hs : Strict A) : Strict (reducedA a g h A) := by
  intro i x y pre
  apply quotientCausal a g h ax gx
  intro j hji
  apply hs
  intro k hkj
  apply sectionCausal a g h ax
  intro l hlk
  exact pre l (by omega)

theorem noDeletedRead (x y : (Fin s → K)) (ah : a ≠ g)
    (agree : ∀ i, i ≠ g → x i=y i) :
    sectionMap a g h x=sectionMap a g h y := by
  funext i
  by_cases ig : i=g
  · simp [sectionMap,ig]
  · by_cases ih : i=h
    · subst i
      simp [sectionMap,ig,agree h ig,agree a ah]
    · simp [sectionMap,ig,ih,agree i ig]

inductive Word where
| unit : Word
| advance : Word → Word
| mul : Word → Word → Word

def grade : Word → Nat
| .unit => 0
| .advance x => grade x+1
| .mul x y => grade x+grade y

def eval (A : (Fin s → K) → (Fin s → K)) (e : (Fin s → K)) : Word → (Fin s → K)
| .unit => e
| .advance t => A (eval A e t)
| .mul t u => prod (eval A e t) (eval A e u)

theorem reducedEval (A : (Fin s → K) → (Fin s → K))
    (ag : a ≠ g) (ah : a ≠ h) (gh : g ≠ h)
    (null : ∀ x, A (cancelled g h x)=A x)
    (latePair : ∀ t : Word, grade t ≤ 6 → eval A oldUnit t g=eval A oldUnit t h)
    (anchor : ∀ t : Word, grade t ≤ 2 → eval A oldUnit t a=eval A oldUnit t g)
    (t : Word) (budget : grade t ≤ 9) :
    eval (reducedA a g h A) (quotient a g h oldUnit) t=quotient a g h (eval A oldUnit t) := by
  induction t with
  | unit => rfl
  | advance t ih =>
    have ht : grade t ≤ 9 := by simp [grade] at budget; omega
    simp only [eval,ih ht,reducedA,sectionQuotient a g h ag ah gh,null]
  | mul t u it iu =>
    have hb : grade t+grade u ≤ 9 := budget
    have ht : grade t ≤ 9 := by omega
    have hu : grade u ≤ 9 := by omega
    have agree : (eval A oldUnit t g=eval A oldUnit t h ∧ eval A oldUnit u g=eval A oldUnit u h) ∨
        (eval A oldUnit t a=eval A oldUnit t g ∧ eval A oldUnit t g=eval A oldUnit t h) ∨
        (eval A oldUnit u a=eval A oldUnit u g ∧ eval A oldUnit u g=eval A oldUnit u h) := by
      by_cases hta : grade t ≤ 6
      · by_cases hua : grade u ≤ 6
        · exact Or.inl ⟨latePair t hta,latePair u hua⟩
        · exact Or.inr (Or.inl ⟨anchor t (by omega),latePair t hta⟩)
      · exact Or.inr (Or.inr ⟨anchor u (by omega),latePair u (by omega)⟩)
    simp only [eval,it ht,iu hu]
    exact (quotientProd a g h gh _ _ agree).symm

theorem reducedRead (A : (Fin s → K) → (Fin s → K)) (L : (Fin s → K) → K)
    (ag : a ≠ g) (ah : a ≠ h) (gh : g ≠ h)
    (null : ∀ x, A (cancelled g h x)=A x)
    (outNull : ∀ x, L (cancelled g h x)=L x)
    (latePair : ∀ t : Word, grade t ≤ 6 → eval A oldUnit t g=eval A oldUnit t h)
    (anchor : ∀ t : Word, grade t ≤ 2 → eval A oldUnit t a=eval A oldUnit t g)
    (t : Word) (budget : grade t ≤ 9) :
    L (sectionMap a g h (eval (reducedA a g h A) (quotient a g h oldUnit) t)) =
      L (eval A oldUnit t) := by
  rw [reducedEval a g h A ag ah gh null latePair anchor t budget,
    sectionQuotient a g h ag ah gh,outNull]

end RKResearch.ERK10SingleGhostLatePairGate
#print axioms RKResearch.ERK10SingleGhostLatePairGate.clockBezout
#print axioms RKResearch.ERK10SingleGhostLatePairGate.noLobattoRatio
#print axioms RKResearch.ERK10SingleGhostLatePairGate.sectionQuotient
#print axioms RKResearch.ERK10SingleGhostLatePairGate.quotientProd
#print axioms RKResearch.ERK10SingleGhostLatePairGate.strictReduced
#print axioms RKResearch.ERK10SingleGhostLatePairGate.noDeletedRead
#print axioms RKResearch.ERK10SingleGhostLatePairGate.reducedEval
#print axioms RKResearch.ERK10SingleGhostLatePairGate.reducedRead
#print axioms RKResearch.ERK10SingleGhostLatePairGate.onlyOrigin
