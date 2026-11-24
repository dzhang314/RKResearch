module

public import RKCert.ERKOrderNineGoodPrimeSplit
public import RKCert.ERKOrderNineH48DiagnosticForms
public import RKCert.ERKGoodPrimeNat

@[expose] public section

/-! # Triangular selection of the surviving ordered root tuple -/
namespace RKCert.GoodPrimeDense
open RKCert.FixedFactor Polynomial

structure NatSplitDatum (p : ℕ) where
  rel : List ℕ
  knots : Fin 4 → List ℕ
  inv : Fin 4 → Fin 4 → Fin 4 → List ℕ

def NatSplitDatum.ops {p : ℕ} (S : NatSplitDatum p) : Operations (List ℕ) :=
  quotient (naturalPrime p) S.rel

noncomputable def NatSplitDatum.factor {p : ℕ} (S : NatSplitDatum p) (E : Type*) [CommRing E] : E[X] :=
  X^S.rel.length - ofCoeffList (S.rel.map (fun k : ℕ => (k:E)))

def NatSplitDatum.splitCheck {p : ℕ} (S : NatSplitDatum p) (d : ℕ) : Prop :=
  pencilPolynomialRecipe S.ops (generator (naturalPrime p)) (constant (naturalPrime p) d) =
    splitRecipe S.ops S.knots

def NatSplitDatum.unitCheck {p : ℕ} (S : NatSplitDatum p) (d : ℕ) (a b c : Fin 4) : Prop :=
  S.ops.mul (terminalRecipe S.ops (S.knots a) (S.knots b) (S.knots c)
    (generator (naturalPrime p)) (constant (naturalPrime p) d)) (S.inv a b c) = [1]

structure NatSelectorDatum (p : ℕ) where
  split : NatSplitDatum p
  hSlot : Fin 4
  uSlot : Fin 4
  vSlot : Fin 4
  hi : Fin 4 → List ℕ
  ui : Fin 4 → List ℕ
  vi : Fin 4 → List ℕ

variable {p : ℕ}

abbrev naturalParameter (p : ℕ) : List ℕ := generator (naturalPrime p)


/-- A coefficient list in the parameter is reduced directly. This avoids
repeating a full quotient multiplication for every Horner shift by L. -/
def naturalParameterValue (S : NatSplitDatum p) (cs : List ℤ) : List ℕ :=
  reduce (naturalPrime p) S.rel (cs.map (intResidue p))

theorem naturalParameterValue_eval {E : Type*} [Field E] [CharP E p] (pn : p≠0) (S : NatSplitDatum p)
    (l : E) (nr : 0 < S.rel.length) (relEq : read (fun n : ℕ => (n:E)) l S.rel = l^S.rel.length)
    (cs : List ℤ) :
    read (fun n : ℕ => (n:E)) l (naturalParameterValue S cs) = read (Int.castRingHom E) l cs := by
  rw [naturalParameterValue,read_reduce (Sound.naturalPrime (R:=E) pn) l nr relEq]
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    simp only [List.map_cons,read,intResidue_cast pn,Int.coe_castRingHom,ih]

def naturalSelectorRecipe0 (S : NatSplitDatum p) (h u v : List ℕ) : List ℕ :=
  computeHorner S.ops (computeHorner S.ops (computeHorner S.ops (naturalParameterValue S) h) u) v intStage0

def naturalSelectorRecipe1 (S : NatSplitDatum p) (h u : List ℕ) : List ℕ :=
  computeHorner S.ops (computeHorner S.ops (naturalParameterValue S) h) u intStage1

def naturalSelectorRecipe2 (S : NatSplitDatum p) (h : List ℕ) : List ℕ :=
  computeHorner S.ops (naturalParameterValue S) h intStage2

section Eval

variable {E : Type*} [Field E] (S : NatSplitDatum p)
  (l : E) (hr : ∀cs, read (fun n : ℕ => (n:E)) l (naturalParameterValue S cs) = read (Int.castRingHom E) l cs)
  (s : Sound S.ops (read (fun n : ℕ => (n:E)) l))
include hr s

theorem naturalSelectorRecipe0_eval (h u v : List ℕ) :
    read (fun n : ℕ => (n:E)) l (naturalSelectorRecipe0 S h u v) = diag0 (Int.castRingHom E) l (read (fun n : ℕ => (n:E)) l h) (read (fun n : ℕ => (n:E)) l u) (read (fun n : ℕ => (n:E)) l v) := by
  simp [naturalSelectorRecipe0,diag0,computeHorner_sound s,Function.comp_def,hr]

theorem naturalSelectorRecipe1_eval (h u : List ℕ) :
    read (fun n : ℕ => (n:E)) l (naturalSelectorRecipe1 S h u) = diag1 (Int.castRingHom E) l (read (fun n : ℕ => (n:E)) l h) (read (fun n : ℕ => (n:E)) l u) := by
  simp [naturalSelectorRecipe1,diag1,computeHorner_sound s,Function.comp_def,hr]

theorem naturalSelectorRecipe2_eval (h : List ℕ) :
    read (fun n : ℕ => (n:E)) l (naturalSelectorRecipe2 S h) = diag2 (Int.castRingHom E) l (read (fun n : ℕ => (n:E)) l h) := by
  simp [naturalSelectorRecipe2,diag2,computeHorner_sound s,Function.comp_def,hr]

end Eval

def NatSelectorDatum.hCheck (S : NatSelectorDatum p) (a : Fin 4) : Prop :=
  S.split.ops.mul (naturalSelectorRecipe2 S.split (S.split.knots a)) (S.hi a) = [1]

def NatSelectorDatum.uCheck (S : NatSelectorDatum p) (b : Fin 4) : Prop :=
  S.split.ops.mul (naturalSelectorRecipe1 S.split
    (S.split.knots S.hSlot) (S.split.knots b)) (S.ui b) = [1]

def NatSelectorDatum.vCheck (S : NatSelectorDatum p) (c : Fin 4) : Prop :=
  S.split.ops.mul (naturalSelectorRecipe0 S.split
    (S.split.knots S.hSlot) (S.split.knots S.uSlot) (S.split.knots c)) (S.vi c) = [1]

structure NatSelectorDatum.Checked (S : NatSelectorDatum p) (d : ℕ) : Prop where
  pos : 0 < S.split.rel.length
  split : S.split.splitCheck d
  h : ∀ a, a≠S.hSlot → S.hCheck a
  u : ∀ b, b≠S.hSlot → b≠S.uSlot → S.uCheck b
  v : ∀ c, c≠S.hSlot → c≠S.uSlot → c≠S.vSlot → S.vCheck c
  terminal : S.split.unitCheck d S.hSlot S.uSlot S.vSlot

set_option maxHeartbeats 800000 in
theorem NatSelectorDatum.terminal_nonzero {E : Type*} [Field E] [CharP E p] (pn : p≠0)
    (S : NatSelectorDatum p) (d : ℕ) (h u v l : E)
    (verify : S.Checked d) (froot : (S.split.factor E).eval l=0)
    (roots : RootSystem (pencilAt l (d:E)) h u v)
    (zeroAux : ∀ j, zEval (diagAux j) ![l,h,u,v]=0) :
    terminalAt h u v l (d:E) ≠ 0 := by
  let base := Sound.naturalPrime (R:=E) pn
  have relEq : read (fun n : ℕ => (n:E)) l S.split.rel = l^S.split.rel.length := by
    unfold NatSplitDatum.factor at froot
    rw [eval_sub,eval_pow,eval_X,sub_eq_zero] at froot
    have eq (a : List ℕ) : (ofCoeffList (a.map (fun n : ℕ => (n:E)))).eval l =
        read (fun n : ℕ => (n:E)) l a := by
      induction a with
      | nil => simp [read]
      | cons n a ih => simp [List.map_cons,ofCoeffList_cons,read,ih]
    rw [eq] at froot
    exact froot.symm
  let f : List ℕ→E := read (fun n : ℕ => (n:E)) l
  let s : Sound S.split.ops f := Sound.quotient base l verify.pos relEq
  have par := naturalParameterValue_eval pn S.split l verify.pos relEq
  have fl : f (naturalParameter p) = l := read_generator base l
  have fd : f (constant (naturalPrime p) d) = (d:E) := read_constant base l _
  have f1 : f [1] = 1 := by simp [f,read]
  have unit {a b : List ℕ} (e : S.split.ops.mul a b = [1]) : f a ≠ 0 := by
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
    change read (fun n : ℕ => (n:E)) l (naturalSelectorRecipe2 S.split (S.split.knots a)) = 0
    rw [naturalSelectorRecipe2_eval S.split l par s]
    have hz := zeroAux (2:Fin 3)
    change zEval diagPoly2 ![l, f (S.split.knots a), f (S.split.knots b), f (S.split.knots c)]=0 at hz
    rwa [zEval_diagPoly2] at hz
  subst a
  have bE : b=S.uSlot := by
    by_contra neq
    apply unit (verify.u b ab.symm neq)
    change read (fun n : ℕ => (n:E)) l (naturalSelectorRecipe1 S.split (S.split.knots S.hSlot) (S.split.knots b)) = 0
    rw [naturalSelectorRecipe1_eval S.split l par s]
    have hz := zeroAux (1:Fin 3)
    change zEval diagPoly1 ![l, f (S.split.knots S.hSlot), f (S.split.knots b),
      f (S.split.knots c)]=0 at hz
    rwa [zEval_diagPoly1] at hz
  subst b
  have cE : c=S.vSlot := by
    by_contra neq
    apply unit (verify.v c ac.symm bc.symm neq)
    change read (fun n : ℕ => (n:E)) l (naturalSelectorRecipe0 S.split (S.split.knots S.hSlot) (S.split.knots S.uSlot) (S.split.knots c)) = 0
    rw [naturalSelectorRecipe0_eval S.split l par s]
    have hz := zeroAux (0:Fin 3)
    change zEval diagPoly0 ![l, f (S.split.knots S.hSlot), f (S.split.knots S.uSlot),
      f (S.split.knots c)]=0 at hz
    rwa [zEval_diagPoly0] at hz
  subst c
  intro z
  apply unit verify.terminal
  rwa [eval_terminalRecipe s,fl,fd]

end RKCert.GoodPrimeDense
