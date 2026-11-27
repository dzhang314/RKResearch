import Lean

/-! Exact finite-grade lower-triangular change of stage coordinates. -/
namespace RKResearch.ERK10ReviveGhostGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0] {s : Nat}
abbrev Vec (K : Type) (sz : Nat) := Fin sz → K
variable (g h : Fin s)

def mix (x : Vec K s) : Vec K s :=
  fun i => if i=h then (x h+x g)/2 else x i
def unmix (x : Vec K s) : Vec K s :=
  fun i => if i=h then 2*x h-x g else x i
def unitVec : Vec K s := fun _ => 1
def prod (x y : Vec K s) : Vec K s := fun i => x i*y i
def basisAt (a : Fin s) : Vec K s := fun i => if i=a then 1 else 0

theorem unmixMix (hg : g ≠ h) (x : Vec K s) : unmix g h (mix g h x)=x := by
  funext i
  by_cases hi : i=h
  · subst i
    simp [unmix,mix,hg]
    grind
  · simp [unmix,mix,hi]

theorem mixUnmix (hg : g ≠ h) (x : Vec K s) : mix g h (unmix g h x)=x := by
  funext i
  by_cases hi : i=h
  · subst i
    simp [unmix,mix,hg]
    grind
  · simp [unmix,mix,hi]

theorem mixUnit : mix g h (unitVec : Vec K s)=unitVec := by
  funext i
  by_cases hi : i=h
  · subst i
    simp [mix,unitVec]
    grind
  · simp [mix,unitVec,hi]

theorem mixProd (x y : Vec K s) (hx : x g=x h ∨ y g=y h) :
    mix g h (prod x y)=prod (mix g h x) (mix g h y) := by
  funext i
  by_cases hi : i=h
  · subst i
    simp [mix,prod]
    cases hx <;> grind
  · simp [mix,prod,hi]

def Strict (A : Vec K s → Vec K s) : Prop :=
  ∀ i x y, (∀ j : Fin s, j.val<i.val → x j=y j) → A x i=A y i
def Causal (A : Vec K s → Vec K s) : Prop :=
  ∀ i x y, (∀ j : Fin s, j.val≤i.val → x j=y j) → A x i=A y i

theorem mixCausal (hh : g.val<h.val) : Causal (mix (K:=K) g h) := by
  intro i x y he
  by_cases hi : i=h
  · subst i
    simp [mix,he h (by omega),he g (by omega)]
  · simp [mix,hi,he i (by omega)]

theorem unmixCausal (hh : g.val<h.val) : Causal (unmix (K:=K) g h) := by
  intro i x y he
  by_cases hi : i=h
  · subst i
    simp [unmix,he h (by omega),he g (by omega)]
  · simp [unmix,hi,he i (by omega)]

def conjugate (A : Vec K s → Vec K s) : Vec K s → Vec K s :=
  fun x => mix g h (A (unmix g h x))

theorem strictConjugate (hh : g.val<h.val) (A : Vec K s → Vec K s) (hs : Strict A) :
    Strict (conjugate g h A) := by
  intro i x y pre
  apply mixCausal (K:=K) g h hh
  intro j hji
  apply hs
  intro k hkj
  apply unmixCausal (K:=K) g h hh
  intro l hlk
  exact pre l (by omega)

theorem unmixGhost (dg : g ≠ h) :
    unmix g h (basisAt g : Vec K s) = fun i => basisAt g i-basisAt h i := by
  funext i
  by_cases hi : i=h
  · subst i
    have dh : h ≠ g := Ne.symm dg
    simp [unmix,basisAt,dh] <;> grind
  · simp [unmix,basisAt,hi] <;> grind

theorem unmixLive (dg : g ≠ h) :
    unmix g h (basisAt h : Vec K s) = fun i => 2*basisAt h i := by
  funext i
  by_cases hi : i=h
  · subst i
    simp [unmix,basisAt,dg] <;> grind
  · simp [unmix,basisAt,hi] <;> grind

theorem unmixOther (a : Fin s) (ag : a ≠ g) (ah : a ≠ h) :
    unmix g h (basisAt a : Vec K s)=basisAt a := by
  funext i
  by_cases hi : i=h
  · subst i
    simp [unmix,basisAt,Ne.symm ag,Ne.symm ah] <;> grind
  · simp [unmix,hi]

def add (x y : Vec K s) : Vec K s := fun i => x i+y i
def scale (a : K) (x : Vec K s) : Vec K s := fun i => a*x i
def IsLinear (A : Vec K s → Vec K s) : Prop :=
  (∀ x y, A (add x y)=add (A x) (A y)) ∧
  (∀ a x, A (scale a x)=scale a (A x))

theorem mixLinear : IsLinear (mix (K:=K) g h) := by
  constructor
  · intro x y
    funext i
    by_cases hi : i=h
    · subst i
      simp [mix,add] <;> grind
    · simp [mix,add,hi]
  · intro a x
    funext i
    by_cases hi : i=h
    · subst i
      simp [mix,scale] <;> grind
    · simp [mix,scale,hi]

theorem unmixLinear : IsLinear (unmix (K:=K) g h) := by
  constructor
  · intro x y
    funext i
    by_cases hi : i=h
    · subst i
      simp [unmix,add] <;> grind
    · simp [unmix,add,hi]
  · intro a x
    funext i
    by_cases hi : i=h
    · subst i
      simp [unmix,scale] <;> grind
    · simp [unmix,scale,hi]

theorem conjugateLinear (A : Vec K s → Vec K s) (hA : IsLinear A) :
    IsLinear (conjugate g h A) := by
  constructor
  · intro x y
    simp only [conjugate,(unmixLinear g h).1,hA.1,(mixLinear g h).1]
  · intro a x
    simp only [conjugate,(unmixLinear g h).2,hA.2,(mixLinear g h).2]

theorem transformedWeights (L : Vec K s → K) (dg : g ≠ h)
    (sub : ∀ x y, L (fun i => x i-y i)=L x-L y)
    (smul : ∀ a x, L (scale a x)=a*L x)
    (ghost : L (basisAt g)=0) (live : L (basisAt h) ≠ 0) :
    L (unmix g h (basisAt g)) ≠ 0 ∧ L (unmix g h (basisAt h)) ≠ 0 ∧
    ∀ i, i ≠ g → i ≠ h → L (unmix g h (basisAt i))=L (basisAt i) := by
  constructor
  · rw [unmixGhost g h dg,sub,ghost]
    grind
  constructor
  · rw [unmixLive g h dg]
    change L (scale 2 (basisAt h)) ≠ 0
    rw [smul]
    grind
  · intro i ig ih
    rw [unmixOther g h i ig ih]

/-- Binary stage expressions: advancing grafts a parent and the product
identifies roots. Every rooted-tree stage expression has this form. -/
inductive Word where
| unit : Word
| advance : Word → Word
| mul : Word → Word → Word

def grade : Word → Nat
| .unit => 0
| .advance x => grade x+1
| .mul x y => grade x+grade y

def eval (A : Vec K s → Vec K s) : Word → Vec K s
| .unit => unitVec
| .advance t => A (eval A t)
| .mul t u => prod (eval A t) (eval A u)

theorem conjugateEval (A : Vec K s → Vec K s)
    (dg : g ≠ h) (agreement : ∀ t : Word, grade t ≤ 4 → eval A t g=eval A t h)
    (t : Word) (budget : grade t ≤ 9) :
    eval (conjugate g h A) t=mix g h (eval A t) := by
  induction t with
  | unit =>
    simpa [eval] using (mixUnit (K:=K) g h).symm
  | advance t ih =>
    have ht : grade t ≤ 9 := by simp [grade] at budget; omega
    simp only [eval,ih ht,conjugate,unmixMix g h dg]
  | mul t u it iu =>
    have hb : grade t+grade u ≤ 9 := budget
    have ht : grade t ≤ 9 := by omega
    have hu : grade u ≤ 9 := by omega
    have agree : eval A t g=eval A t h ∨ eval A u g=eval A u h := by
      by_cases hlow : grade t ≤ 4
      · exact Or.inl (agreement t hlow)
      · exact Or.inr (agreement u (by omega))
    simp only [eval,it ht,iu hu]
    exact (mixProd g h _ _ agree).symm

theorem transportRead (A : Vec K s → Vec K s) (L : Vec K s → K)
    (dg : g ≠ h) (agreement : ∀ t : Word, grade t ≤ 4 → eval A t g=eval A t h)
    (t : Word) (budget : grade t ≤ 9) :
    L (unmix g h (eval (conjugate g h A) t))=L (eval A t) := by
  rw [conjugateEval g h A dg agreement t budget,unmixMix g h dg]

end RKResearch.ERK10ReviveGhostGate
#print axioms RKResearch.ERK10ReviveGhostGate.unmixMix
#print axioms RKResearch.ERK10ReviveGhostGate.mixUnmix
#print axioms RKResearch.ERK10ReviveGhostGate.mixProd
#print axioms RKResearch.ERK10ReviveGhostGate.strictConjugate
#print axioms RKResearch.ERK10ReviveGhostGate.unmixGhost
#print axioms RKResearch.ERK10ReviveGhostGate.unmixLive
#print axioms RKResearch.ERK10ReviveGhostGate.unmixOther
#print axioms RKResearch.ERK10ReviveGhostGate.conjugateEval
#print axioms RKResearch.ERK10ReviveGhostGate.transportRead
#print axioms RKResearch.ERK10ReviveGhostGate.mixLinear
#print axioms RKResearch.ERK10ReviveGhostGate.unmixLinear
#print axioms RKResearch.ERK10ReviveGhostGate.conjugateLinear
#print axioms RKResearch.ERK10ReviveGhostGate.transformedWeights
