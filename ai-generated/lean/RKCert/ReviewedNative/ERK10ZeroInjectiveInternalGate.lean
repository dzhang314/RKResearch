import Lean

/-! Exact fifth-row commutator and weighted repeat ratio for the
one-ghost injective-F4 exclusion. -/
namespace RKResearch.ERK10ZeroInjectiveInternalGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem fifthContrast (t p a43 a53 a54 r3 r4 r5 : K)
    (plain : r4*(a53*r3+a54*r4)-r5*(a43*r3)=0) :
    r4*(a53*t*r3+a54*p*r4)-r5*(a43*t*r3) =
       (p-t)*a54*r4^2 := by
  calc
    _=t*(r4*(a53*r3+a54*r4)-r5*(a43*r3))+(p-t)*a54*r4^2 := by
        clear plain
        grind
    _=_ := by rw [plain]; grind

theorem trueFifthChange (t p a change : K)
    (ht : t ≠ 0) (hp : p=2*t)
    (timed : t*change=3*p*(p-t)*a) : change=3*p*a := by
  have e : t*(change-3*p*a)=0 := by grind
  grind

theorem responseRatio (t a r3 r4 : K)
    (tLive : t ≠ 0) (aLive : a ≠ 0)
    (first : 2*a*r3=t^2)
    (second : 2*a*t*r4=(2*t)^2*(3*t-2*(2*t))) :
    r4=-4*r3 := by
  have q : (2*a*t)*(r4+4*r3)=0 := by grind
  grind

theorem supportTooSmall (q : Nat) (potential : 6≤11-2*q) : q≤2 := by omega

def L (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def derivL (x : K) : K := 168*x^3-252*x^2+112*x-14
def planted (x : K) : K := 252*x^3-392*x^2+182*x-23
theorem halfContact (x : K) :
    2*(x*derivL x-8*L (x/2))=7*L x+planted x := by
  unfold L derivL planted
  grind
theorem halfBezout (x : K) :
    (-273672*x^2+268968*x-50848)*L x+
    (45612*x^3-65100*x^2+24738*x-2263)*planted x=1201 := by
  unfold L planted
  grind
theorem noHalfContact (x : K) (root : L x=0)
    (contact : x*derivL x=8*L (x/2)) : False := by
  have eq := halfContact x
  have bz := halfBezout x
  grind

end RKResearch.ERK10ZeroInjectiveInternalGate
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.fifthContrast
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.trueFifthChange
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.responseRatio
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.supportTooSmall

namespace RKResearch.ERK10ZeroInjectiveInternalGate.Relocation
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0] {n : Nat}
variable (g i j : Fin n)
def swap (x : Fin n → K) : Fin n → K :=
  fun k => if k=j then x g+x i-x j else x k
def vOne : Fin n → K := fun _ => 1
def add (x y : Fin n → K) : Fin n → K := fun k => x k+y k
def scale (a : K) (x : Fin n → K) : Fin n → K := fun k => a*x k
def prod (x y : Fin n → K) : Fin n → K := fun k => x k*y k
def basis (k : Fin n) : Fin n → K := fun h => if h=k then 1 else 0

theorem swapSwap (gj : g ≠ j) (ij : i ≠ j) (x : Fin n → K) :
    swap g i j (swap g i j x)=x := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,gj,ij] <;> grind
  · simp [swap,eq]

theorem swapUnit : swap g i j (vOne (K:=K) (n:=n))=vOne := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,vOne] <;> grind
  · simp [swap,vOne,eq]

theorem swapAdd (x y : Fin n → K) :
    swap g i j (add x y)=add (swap g i j x) (swap g i j y) := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,add] <;> grind
  · simp [swap,add,eq]

theorem swapScale (a : K) (x : Fin n → K) :
    swap g i j (scale a x)=scale a (swap g i j x) := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,scale] <;> grind
  · simp [swap,scale,eq]

theorem swapProduct (x y : Fin n → K)
    (eligible : (x i=x j ∧ y i=y j) ∨
      (x g=x i ∧ x i=x j) ∨ (y g=y i ∧ y i=y j)) :
    swap g i j (prod x y)=prod (swap g i j x) (swap g i j y) := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,prod]
    rcases eligible with a | b | c <;> grind
  · simp [swap,prod,eq]

def Strict (A : (Fin n → K) → Fin n → K) : Prop :=
  ∀ k x y, (∀ t : Fin n, t.val<k.val → x t=y t) → A x k=A y k
def Causal (A : (Fin n → K) → Fin n → K) : Prop :=
  ∀ k x y, (∀ t : Fin n, t.val≤k.val → x t=y t) → A x k=A y k

theorem swapCausal (gj : g.val<j.val) (ij : i.val<j.val) :
    Causal (swap (K:=K) g i j) := by
  intro k x y pre
  by_cases eq : k=j
  · subst k
    simp [swap,pre g (by omega),pre i (by omega),pre j (by omega)]
  · simp [swap,eq,pre k (by omega)]

def conjugate (A : (Fin n → K) → Fin n → K) : (Fin n → K) → Fin n → K :=
  fun x => swap g i j (A (swap g i j x))

theorem strictConjugate (gj : g.val<j.val) (ij : i.val<j.val)
    (A : (Fin n → K) → Fin n → K) (ha : Strict A) :
    Strict (conjugate g i j A) := by
  intro k x y pre
  apply swapCausal g i j gj ij
  intro t ht
  apply ha
  intro u hu
  apply swapCausal g i j gj ij
  intro v hv
  exact pre v (by omega)

theorem basisGhost (gi : g ≠ i) (gj : g ≠ j) (_ij : i ≠ j) :
    swap g i j (basis g : Fin n → K)=add (basis g) (basis j) := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,basis,add,Ne.symm gi,Ne.symm gj] <;> grind
  · simp [swap,add,basis,eq] <;> grind

theorem basisEarly (gi : g ≠ i) (_gj : g ≠ j) (ij : i ≠ j) :
    swap g i j (basis i : Fin n → K)=add (basis i) (basis j) := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,basis,add,gi,Ne.symm ij] <;> grind
  · simp [swap,add,basis,eq] <;> grind

theorem basisLate (gj : g ≠ j) (ij : i ≠ j) :
    swap g i j (basis j : Fin n → K)=scale (-1) (basis j) := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,basis,scale,gj,ij] <;> grind
  · simp [swap,basis,scale,eq] <;> grind

theorem basisOther (x : Fin n) (xg : x ≠ g) (xi : x ≠ i) (xj : x ≠ j) :
    swap g i j (basis x : Fin n → K)=basis x := by
  funext k
  by_cases eq : k=j
  · subst k
    simp [swap,basis,Ne.symm xg,Ne.symm xi,Ne.symm xj] <;> grind
  · simp [swap,basis,eq]

theorem noCarrierMultiple (gi : g ≠ i) (gj : g ≠ j) (ij : i ≠ j)
    (carrier : Fin n → K) (atGhost : carrier g=1) (a : K) :
    swap g i j (basis i : Fin n → K) ≠ scale a carrier := by
  intro bad
  rw [basisEarly g i j gi gj ij] at bad
  have a0 : a=0 := by
    have h := congrFun bad g
    simp [basis,add,scale,gi,gj,atGhost] at h
    grind
  have h := congrFun bad i
  simp [basis,add,scale,a0,ij] at h
  grind

theorem outputRelocates (gi : g ≠ i) (gj : g ≠ j) (ij : i ≠ j)
    (L : (Fin n → K) → K)
    (linearAdd : ∀ x y, L (add x y)=L x+L y)
    (linearScale : ∀ a x, L (scale a x)=a*L x)
    (ghost : L (basis g)=0) (opposing : L (basis i)+L (basis j)=0)
    (late : L (basis j) ≠ 0) :
    L (swap g i j (basis g)) ≠ 0 ∧ L (swap g i j (basis i))=0 ∧
    L (swap g i j (basis j)) ≠ 0 ∧
    ∀ k, k ≠ g → k ≠ i → k ≠ j → L (swap g i j (basis k))=L (basis k) := by
  constructor
  · rw [basisGhost g i j gi gj ij,linearAdd,ghost]
    grind
  constructor
  · rw [basisEarly g i j gi gj ij,linearAdd,opposing]
  constructor
  · rw [basisLate g i j gj ij,linearScale]
    grind
  · intro k kg ki kj
    rw [basisOther g i j k kg ki kj]

inductive Word where
| unit : Word
| advance : Word → Word
| mul : Word → Word → Word
def grade : Word → Nat
| .unit => 0
| .advance t => grade t+1
| .mul t u => grade t+grade u
def eval (A : (Fin n → K) → Fin n → K) : Word → Fin n → K
| .unit => vOne
| .advance t => A (eval A t)
| .mul t u => prod (eval A t) (eval A u)

theorem transport (A : (Fin n → K) → Fin n → K)
    (gj : g ≠ j) (ij : i ≠ j)
    (lateMatch : ∀ t, grade t≤7 → eval A t i=eval A t j)
    (ghostTag : ∀ t, grade t≤1 → eval A t g=eval A t i)
    (t : Word) (pay : grade t≤9) :
    eval (conjugate g i j A) t=swap g i j (eval A t) := by
  induction t with
  | unit => simpa [eval] using (swapUnit (K:=K) g i j).symm
  | advance t ih =>
    have h : grade t≤9 := by simp [grade] at pay; omega
    simp only [eval,ih h,conjugate,swapSwap g i j gj ij]
  | mul t u it iu =>
    have h : grade t+grade u≤9 := pay
    have lowT : grade t≤9 := by omega
    have lowU : grade u≤9 := by omega
    have e : (eval A t i=eval A t j ∧ eval A u i=eval A u j) ∨
        (eval A t g=eval A t i ∧ eval A t i=eval A t j) ∨
        (eval A u g=eval A u i ∧ eval A u i=eval A u j) := by
      by_cases sevenT : grade t≤7
      · by_cases sevenU : grade u≤7
        · exact Or.inl ⟨lateMatch t sevenT,lateMatch u sevenU⟩
        · exact Or.inr (Or.inl ⟨ghostTag t (by omega),lateMatch t sevenT⟩)
      · exact Or.inr (Or.inr ⟨ghostTag u (by omega),lateMatch u (by omega)⟩)
    simp only [eval,it lowT,iu lowU]
    exact (swapProduct g i j _ _ e).symm

theorem transportOutput (A : (Fin n → K) → Fin n → K)
    (L : (Fin n → K) → K) (gj : g ≠ j) (ij : i ≠ j)
    (lateMatch : ∀ t, grade t≤7 → eval A t i=eval A t j)
    (ghostTag : ∀ t, grade t≤1 → eval A t g=eval A t i)
    (t : Word) (pay : grade t≤9) :
    L (swap g i j (eval (conjugate g i j A) t)) = L (eval A t) := by
  rw [transport g i j A gj ij lateMatch ghostTag t pay,swapSwap g i j gj ij]

end RKResearch.ERK10ZeroInjectiveInternalGate.Relocation
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.swapSwap
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.swapAdd
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.swapScale
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.swapProduct
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.strictConjugate
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.noCarrierMultiple
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.outputRelocates
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.transport
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.Relocation.transportOutput
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.halfContact
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.halfBezout
#print axioms RKResearch.ERK10ZeroInjectiveInternalGate.noHalfContact
