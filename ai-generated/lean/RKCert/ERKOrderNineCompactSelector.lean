module

public import RKCert.ERKCompactResidueSound
public import RKCert.ERKOrderNineGoodPrimeNatSelector

@[expose] public section

namespace RKCert.CompactResidue

open Polynomial RKCert.GoodPrimeDense RKCert.FixedFactor

def argument (p : ℕ) (cs : List ℤ) : Term := .raw (cs.map (intResidue p))

def diagnostic0 (p : ℕ) (h u v : Term) : Term :=
  computeHorner (syntaxOps p)
    (computeHorner (syntaxOps p) (computeHorner (syntaxOps p) (argument p) h) u) v intStage0

def diagnostic1 (p : ℕ) (h u : Term) : Term :=
  computeHorner (syntaxOps p) (computeHorner (syntaxOps p) (argument p) h) u intStage1

def diagnostic2 (p : ℕ) (h : Term) : Term :=
  computeHorner (syntaxOps p) (argument p) h intStage2

variable {p : ℕ}

def slot (S : NatSelectorDatum p) (a : Fin 4) : Term := .raw (S.split.knots a)

structure TapeChecked (S : NatSelectorDatum p) (d : ℕ) : Prop where
  split : SameValues p S.split.rel
    (pencilPolynomialRecipe (syntaxOps p) (.raw [0,1]) (.raw [d]))
    (splitRecipe (syntaxOps p) (slot S))
  h : ∀ a, a ≠ S.hSlot →
    Value p S.split.rel ((diagnostic2 p (slot S a)).times (.raw (S.hi a))) [1]
  u : ∀ b, b ≠ S.hSlot → b ≠ S.uSlot →
    Value p S.split.rel ((diagnostic1 p (slot S S.hSlot) (slot S b)).times (.raw (S.ui b))) [1]
  v : ∀ c, c ≠ S.hSlot → c ≠ S.uSlot → c ≠ S.vSlot →
    Value p S.split.rel
      ((diagnostic0 p (slot S S.hSlot) (slot S S.uSlot) (slot S c)).times (.raw (S.vi c))) [1]
  terminal : Value p S.split.rel
    ((terminalRecipe (syntaxOps p) (slot S S.hSlot) (slot S S.uSlot) (slot S S.vSlot)
      (.raw [0,1]) (.raw [d])).times (.raw (S.split.inv S.hSlot S.uSlot S.vSlot))) [1]

section Evaluation

variable {E : Type*} [CommRing E] [CharP E p] (hp : p ≠ 0) (l : E)
include hp

private theorem eval_argument (cs : List ℤ) :
    (argument p cs).eval l = GoodPrimeDense.read (Int.castRingHom E) l cs := by
  simp only [argument,Term.eval]
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    simp only [List.map_cons,GoodPrimeDense.read,intResidue_cast hp,Int.coe_castRingHom,ih]

theorem diagnostic0_eval (h u v : Term) :
    (diagnostic0 p h u v).eval l = diag0 (Int.castRingHom E) l (h.eval l) (u.eval l) (v.eval l) := by
  simp [diagnostic0,diag0,computeHorner_sound (syntax_sound hp l),Function.comp_def,eval_argument hp]

theorem diagnostic1_eval (h u : Term) :
    (diagnostic1 p h u).eval l = diag1 (Int.castRingHom E) l (h.eval l) (u.eval l) := by
  simp [diagnostic1,diag1,computeHorner_sound (syntax_sound hp l),Function.comp_def,eval_argument hp]

theorem diagnostic2_eval (h : Term) :
    (diagnostic2 p h).eval l = diag2 (Int.castRingHom E) l (h.eval l) := by
  simp [diagnostic2,diag2,computeHorner_sound (syntax_sound hp l),Function.comp_def,eval_argument hp]

theorem nonzero_of_inverse [Nontrivial E] {r : List Nat} {x y : Term}
    (root : GoodPrimeDense.read (fun n : Nat => (n:E)) l r = l^r.length)
    (verify : Value p r (x.times y) [1]) :
    x.eval l ≠ 0 := by
  have eq := verify.correct l root
  rw [show (x.times y).eval l = x.eval l * y.eval l from (syntax_sound hp l).mul x y] at eq
  intro h
  simp [h,GoodPrimeDense.read] at eq

end Evaluation

set_option maxHeartbeats 800000 in
theorem TapeChecked.terminal_nonzero {E : Type*} [Field E] [CharP E p] (hp : p≠0)
    {S : NatSelectorDatum p} {d : ℕ} (h u v l : E)
    (verify : TapeChecked S d) (froot : (S.split.factor E).eval l=0)
    (roots : RootSystem (pencilAt l (d:E)) h u v)
    (zeroAux : ∀ j, zEval (diagAux j) ![l,h,u,v]=0) :
    terminalAt h u v l (d:E) ≠ 0 := by
  have relEq : GoodPrimeDense.read (fun n : ℕ => (n:E)) l S.split.rel = l^S.split.rel.length := by
    unfold NatSplitDatum.factor at froot
    rw [eval_sub,eval_pow,eval_X,sub_eq_zero] at froot
    have e := (eval_poly E S.split.rel l).symm
    simpa only [polynomial,decode,←froot] using e
  let f : Term → E := Term.eval l
  let s : Sound (syntaxOps p) f := syntax_sound hp l
  have fl : f (.raw [0,1]) = l := by simp [f,Term.eval,GoodPrimeDense.read]
  have fd : f (.raw [d]) = (d:E) := by simp [f,Term.eval,GoodPrimeDense.read]
  have sq : decode f (pencilPolynomialRecipe (syntaxOps p) (.raw [0,1]) (.raw [d])) =
      decode f (splitRecipe (syntaxOps p) (slot S)) :=
    congrArg ofCoeffList (verify.split.correct l relEq)
  rw [decode_pencilPolynomialRecipe s,decode_splitRecipe s,fl,fd] at sq
  obtain ⟨a,b,c,ab,ac,bc,rfl,rfl,rfl⟩ := slots_of_rootSystem (fun i=>f (slot S i)) sq roots
  have aE : a=S.hSlot := by
    by_contra neq
    apply nonzero_of_inverse hp l relEq (verify.h a neq)
    rw [diagnostic2_eval hp]
    have hz := zeroAux (2:Fin 3)
    change zEval diagPoly2 ![l, f (slot S a), f (slot S b), f (slot S c)]=0 at hz
    rwa [zEval_diagPoly2] at hz
  subst a
  have bE : b=S.uSlot := by
    by_contra neq
    apply nonzero_of_inverse hp l relEq (verify.u b ab.symm neq)
    rw [diagnostic1_eval hp]
    have hz := zeroAux (1:Fin 3)
    change zEval diagPoly1 ![l, f (slot S S.hSlot), f (slot S b), f (slot S c)]=0 at hz
    rwa [zEval_diagPoly1] at hz
  subst b
  have cE : c=S.vSlot := by
    by_contra neq
    apply nonzero_of_inverse hp l relEq (verify.v c ac.symm bc.symm neq)
    rw [diagnostic0_eval hp]
    have hz := zeroAux (0:Fin 3)
    change zEval diagPoly0 ![l, f (slot S S.hSlot), f (slot S S.uSlot), f (slot S c)]=0 at hz
    rwa [zEval_diagPoly0] at hz
  subst c
  intro z
  apply nonzero_of_inverse hp l relEq verify.terminal
  change f (terminalRecipe (syntaxOps p) (slot S S.hSlot) (slot S S.uSlot) (slot S S.vSlot)
    (.raw [0,1]) (.raw [d])) = 0
  rwa [eval_terminalRecipe s,fl,fd]

end RKCert.CompactResidue
