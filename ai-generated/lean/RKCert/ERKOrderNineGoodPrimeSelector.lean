module

public import RKCert.ERKOrderNineGoodPrimeSplit
public import RKCert.ERKOrderNineH48DiagnosticForms

@[expose] public section

/-! # Triangular selection of the surviving ordered root tuple -/
namespace RKCert.GoodPrimeDense
open RKCert.FixedFactor Polynomial

structure SelectorDatum (p : ℕ) where
  split : SplitDatum p
  hSlot : Fin 4
  uSlot : Fin 4
  vSlot : Fin 4
  hi : Fin 4 → List (ZMod p)
  ui : Fin 4 → List (ZMod p)
  vi : Fin 4 → List (ZMod p)

variable {p : ℕ}

abbrev parameter (p : ℕ) : List (ZMod p) := generator (scalar (ZMod p))


/-- A coefficient list in the parameter is reduced directly. This avoids
repeating a full quotient multiplication for every Horner shift by L. -/
def parameterValue (S : SplitDatum p) (cs : List ℤ) : List (ZMod p) :=
  reduce (scalar (ZMod p)) S.rel (cs.map (fun c : ℤ => (c:ZMod p)))

theorem parameterValue_eval {E : Type*} [Field E] (S : SplitDatum p) (ψ : ZMod p→+*E)
    (l : E) (nr : 0 < S.rel.length) (relEq : read ψ l S.rel = l^S.rel.length)
    (cs : List ℤ) :
    read ψ l (parameterValue S cs) = read (Int.castRingHom E) l cs := by
  rw [parameterValue,read_reduce (Sound.scalar ψ) l nr relEq]
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    simp only [List.map_cons,read,map_intCast,Int.coe_castRingHom,ih]

def selectorRecipe0 (S : SplitDatum p) (h u v : List (ZMod p)) : List (ZMod p) :=
  computeHorner S.ops (computeHorner S.ops (computeHorner S.ops (parameterValue S) h) u) v intStage0

def selectorRecipe1 (S : SplitDatum p) (h u : List (ZMod p)) : List (ZMod p) :=
  computeHorner S.ops (computeHorner S.ops (parameterValue S) h) u intStage1

def selectorRecipe2 (S : SplitDatum p) (h : List (ZMod p)) : List (ZMod p) :=
  computeHorner S.ops (parameterValue S) h intStage2

section Eval

variable {E : Type*} [Field E] (S : SplitDatum p) (ψ : ZMod p→+*E)
  (l : E) (hr : ∀cs, read ψ l (parameterValue S cs) = read (Int.castRingHom E) l cs)
  (s : Sound S.ops (read ψ l))
include hr s

theorem selectorRecipe0_eval (h u v : List (ZMod p)) :
    read ψ l (selectorRecipe0 S h u v) = diag0 (Int.castRingHom E) l (read ψ l h) (read ψ l u) (read ψ l v) := by
  simp [selectorRecipe0,diag0,computeHorner_sound s,Function.comp_def,hr]

theorem selectorRecipe1_eval (h u : List (ZMod p)) :
    read ψ l (selectorRecipe1 S h u) = diag1 (Int.castRingHom E) l (read ψ l h) (read ψ l u) := by
  simp [selectorRecipe1,diag1,computeHorner_sound s,Function.comp_def,hr]

theorem selectorRecipe2_eval (h : List (ZMod p)) :
    read ψ l (selectorRecipe2 S h) = diag2 (Int.castRingHom E) l (read ψ l h) := by
  simp [selectorRecipe2,diag2,computeHorner_sound s,Function.comp_def,hr]

end Eval

def SelectorDatum.hCheck (S : SelectorDatum p) (a : Fin 4) : Prop :=
  S.split.ops.mul (selectorRecipe2 S.split (S.split.knots a)) (S.hi a) = [1]

def SelectorDatum.uCheck (S : SelectorDatum p) (b : Fin 4) : Prop :=
  S.split.ops.mul (selectorRecipe1 S.split
    (S.split.knots S.hSlot) (S.split.knots b)) (S.ui b) = [1]

def SelectorDatum.vCheck (S : SelectorDatum p) (c : Fin 4) : Prop :=
  S.split.ops.mul (selectorRecipe0 S.split
    (S.split.knots S.hSlot) (S.split.knots S.uSlot) (S.split.knots c)) (S.vi c) = [1]

structure SelectorDatum.Checked (S : SelectorDatum p) (d : ZMod p) : Prop where
  pos : 0 < S.split.rel.length
  split : S.split.splitCheck d
  h : ∀ a, a≠S.hSlot → S.hCheck a
  u : ∀ b, b≠S.hSlot → b≠S.uSlot → S.uCheck b
  v : ∀ c, c≠S.hSlot → c≠S.uSlot → c≠S.vSlot → S.vCheck c
  terminal : S.split.unitCheck d S.hSlot S.uSlot S.vSlot

set_option maxHeartbeats 800000 in
theorem SelectorDatum.terminal_nonzero {E : Type*} [Field E]
    (S : SelectorDatum p) (ψ : ZMod p→+*E) (d : ZMod p) (h u v l : E)
    (verify : S.Checked d) (froot : (S.split.factor.map ψ).eval l=0)
    (roots : RootSystem (pencilAt l (ψ d)) h u v)
    (zeroAux : ∀ j, zEval (diagAux j) ![l,h,u,v]=0) :
    terminalAt h u v l (ψ d) ≠ 0 := by
  let base := Sound.scalar ψ
  have relEq : read ψ l S.split.rel = l^S.split.rel.length := by
    unfold SplitDatum.factor at froot
    rw [Polynomial.map_sub,Polynomial.map_pow,map_X,eval_sub,eval_pow,eval_X,
      ←eval₂_eq_eval_map,eval₂_ofCoeffList_read,sub_eq_zero] at froot
    exact froot.symm
  let f : List (ZMod p)→E := read ψ l
  let s : Sound S.split.ops f := Sound.quotient base l verify.pos relEq
  have par := parameterValue_eval S.split ψ l verify.pos relEq
  have fl : f (parameter p) = l := read_generator base l
  have fd : f (constant (scalar _) d) = ψ d := read_constant base l _
  have f1 : f [1] = 1 := by simp [f,read]
  have unit {a b : List (ZMod p)} (e : S.split.ops.mul a b = [1]) : f a ≠ 0 := by
    intro zero
    have z := congrArg f e
    rw [s.mul,zero,zero_mul,f1] at z
    exact zero_ne_one z
  have sq := congrArg (decode f) verify.split
  rw [decode_pencilPolynomialRecipe s,decode_splitRecipe s,fl,fd] at sq
  obtain ⟨a,b,c,ab,ac,bc,rfl,rfl,rfl⟩ :=
    slots_of_rootSystem (fun i=>f (S.split.knots i)) sq roots
  have aE : a=S.hSlot := by
    by_contra neq
    apply unit (verify.h a neq)
    change read ψ l (selectorRecipe2 S.split (S.split.knots a)) = 0
    rw [selectorRecipe2_eval S.split ψ l par s]
    have hz := zeroAux (2:Fin 3)
    change zEval diagPoly2 ![l, f (S.split.knots a), f (S.split.knots b), f (S.split.knots c)]=0 at hz
    rwa [zEval_diagPoly2] at hz
  subst a
  have bE : b=S.uSlot := by
    by_contra neq
    apply unit (verify.u b ab.symm neq)
    change read ψ l (selectorRecipe1 S.split (S.split.knots S.hSlot) (S.split.knots b)) = 0
    rw [selectorRecipe1_eval S.split ψ l par s]
    have hz := zeroAux (1:Fin 3)
    change zEval diagPoly1 ![l, f (S.split.knots S.hSlot), f (S.split.knots b),
      f (S.split.knots c)]=0 at hz
    rwa [zEval_diagPoly1] at hz
  subst b
  have cE : c=S.vSlot := by
    by_contra neq
    apply unit (verify.v c ac.symm bc.symm neq)
    change read ψ l (selectorRecipe0 S.split (S.split.knots S.hSlot) (S.split.knots S.uSlot) (S.split.knots c)) = 0
    rw [selectorRecipe0_eval S.split ψ l par s]
    have hz := zeroAux (0:Fin 3)
    change zEval diagPoly0 ![l, f (S.split.knots S.hSlot), f (S.split.knots S.uSlot),
      f (S.split.knots c)]=0 at hz
    rwa [zEval_diagPoly0] at hz
  subst c
  intro z
  apply unit verify.terminal
  rwa [eval_terminalRecipe s,fl,fd]

end RKCert.GoodPrimeDense
