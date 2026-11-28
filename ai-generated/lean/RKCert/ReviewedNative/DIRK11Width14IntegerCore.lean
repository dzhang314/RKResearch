module

public import RKCert.ReviewedNative.SufficientGradedFlags
public import RKCert.ReviewedNative.QuadTowerIntReplay
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

@[expose] public section

/-! Integer graded closure certificate for a width-fourteen DIRK tableau.
All coefficient arithmetic is performed before specialization. Each linear
combination has one clearing scale; no rational gcd is in the checker. -/
namespace RKResearch.Certified.DIRK11Width14IntegerCore
open RKResearch FiniteRootedTree Graded QuadTowerIntReplay
open scoped Matrix BigOperators FiniteRootedTree

structure Witness where
  scalePred : Nat
  coefficients : Nat → C16

structure IndexWitness where
  scalePred : Nat
  coefficients : Array Nat

structure Packet where
  red : Reductions
  denominatorPred : Nat
  a : Nat → Nat → C16
  b : Nat → C16
  clock : Nat → C16
  size : Nat → Nat
  basis : Nat → Nat → Nat → C16
  nextA : Nat → Nat → Witness
  nextC : Nat → Nat → Witness
  product : Nat → Nat → Nat → Nat → Witness
  primitive : Nat → Witness
  failureInverse : C16
  failureDenPred : Nat

abbrev V := Fin 14 → C16

def Packet.den (P : Packet) : Nat := P.denominatorPred+1

def smul (D : Reductions) (x y : C16) : C16 :=
  if x = pack 0 then pack 0
  else if y = pack 0 then pack 0
  else if x = pack 1 then y
  else if y = pack 1 then x
  else mul D x y

def csum : {n : Nat} → (Fin n → C16) → C16
  | 0, _ => pack 0
  | n+1, f => add (f 0) (csum (fun j : Fin n => f j.succ))

def power (D : Reductions) (x : C16) : Nat → C16
  | 0 => pack 1
  | n+1 => smul D (power D x n) x

def rawMatrix (P : Packet) (i j : Fin 14) : C16 :=
  if i < j then pack 0 else P.a i.val j.val
def rawBeta (P : Packet) : V := fun i => P.b i.val
def node (P : Packet) : V := fun i => P.clock i.val
def one : V := fun _ => pack 1
def powC (P : Packet) (j : Nat) : V := fun i => power P.red (node P i) j
def gen (P : Packet) (d : Nat) (i : Fin (P.size d)) : V := fun j => P.basis d i.val j.val

def subV (u v : V) : V := fun i => add (u i) (sc (-1) (v i))
def mulV (P : Packet) (u v : V) : V := fun i => smul P.red (u i) (v i)
def scaleV (n : Nat) (u : V) : V := fun i => sc (n:Int) (u i)
def act (P : Packet) (v : V) : V :=
  fun i => csum fun j => smul P.red (rawMatrix P i j) (v j)
def out (P : Packet) (v : V) : C16 := csum fun j => smul P.red (rawBeta P j) (v j)
def combo (P : Packet) (d : Nat) (c : Nat → C16) : V :=
  fun i => csum fun j : Fin (P.size d) => smul P.red (c j.val) (gen P d j i)

def eqV (v w : V) : Bool := (List.finRange 14).all fun i => decide (v i = w i)
def checkNode (P : Packet) : Bool := eqV (act P one) (node P)
def checkCombo (P : Packet) (d : Nat) (v : V) (w : Witness) : Bool :=
  eqV (scaleV (w.scalePred+1) v) (combo P d w.coefficients)
def checkA (P : Packet) (d : Nat) (i : Fin (P.size d)) : Bool :=
  checkCombo P (d+1) (act P (gen P d i)) (P.nextA d i.val)
def checkC (P : Packet) (d : Nat) (i : Fin (P.size d)) : Bool :=
  checkCombo P (d+1) (mulV P (node P) (gen P d i)) (P.nextC d i.val)
def checkProduct (P : Packet) (d e : Nat) (i : Fin (P.size d)) (j : Fin (P.size e)) : Bool :=
  checkCombo P (d+e) (mulV P (gen P d i) (gen P e j)) (P.product d e i.val j.val)
def primitiveV (P : Packet) (d : Nat) : V :=
  subV (scaleV (d+1) (act P (powC P d))) (powC P (d+1))
def checkPrimitive (P : Packet) (d : Nat) : Bool :=
  checkCombo P (d+1) (primitiveV P d) (P.primitive d)
def checkSilent (P : Packet) (d : Nat) (i : Fin (P.size d)) : Bool :=
  decide (out P (gen P d i) = pack 0)
def checkScalar (P : Packet) (d : Nat) : Bool :=
  decide (sc (d+1:Nat) (out P (powC P d)) = pack ((P.den:Int)^(d+1)))
def failureNumerator (P : Packet) : C16 :=
  add (sc 84 (out P (mulV P (powC P 4) (act P (powC P 6))))) (pack (-(P.den:Int)^12))
def checkFailure (P : Packet) : Bool :=
  decide (smul P.red (failureNumerator P) P.failureInverse = pack (P.failureDenPred+1:Nat))

structure Receipts (P : Packet) : Prop where
  node : checkNode P = true
  stepA : ∀ d < 10, ∀ i, checkA P d i = true
  stepC : ∀ d < 10, ∀ i, checkC P d i = true
  product : ∀ d e, d+e < 11 → ∀ i j, checkProduct P d e i j = true
  primitive : ∀ d < 10, checkPrimitive P d = true
  silent : ∀ d < 11, ∀ i, checkSilent P d i = true
  scalar : ∀ d < 11, checkScalar P d = true
  failure : checkFailure P = true

section Generic
variable {R : Type*} [Field R] [CharZero R]
variable {P : Packet} {x y z w : R}

omit [CharZero R] in
theorem eval_mul (h : Roots P.red x y z w) (u v : C16) :
    val x y z w (smul P.red u v) = val x y z w u * val x y z w v := by
  unfold smul
  split
  next h0 => simp [h0]
  next =>
    split
    next h0 => simp [h0]
    next =>
      split
      next h1 => simp [h1]
      next =>
        split
        next h1 => simp [h1]
        next => exact val_mul h u v

omit [CharZero R] in
theorem eval_sum {n : Nat} (f : Fin n → C16) :
    val x y z w (csum f) = ∑ i, val x y z w (f i) := by
  induction n with
  | zero => simp [csum]
  | succ n ih => simp only [csum,val_add,ih,Fin.sum_univ_succ]

omit [CharZero R] in
theorem eval_pow (h : Roots P.red x y z w) (u : C16) (n : Nat) :
    val x y z w (power P.red u n) = (val x y z w u)^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp only [power,eval_mul h,ih,pow_succ]

def ev (x y z w : R) (v : V) : Fin 14 → R := fun i => val x y z w (v i)
def intA (P : Packet) (x y z w : R) : Matrix (Fin 14) (Fin 14) R :=
  fun i j => val x y z w (rawMatrix P i j)
def intB (P : Packet) (x y z w : R) : Fin 14 → R := ev x y z w (rawBeta P)

def A (P : Packet) (x y z w : R) : Matrix (Fin 14) (Fin 14) R :=
  ((P.den:R)⁻¹) • intA P x y z w
def b (P : Packet) (x y z w : R) : Fin 14 → R := ((P.den:R)⁻¹) • intB P x y z w

theorem den_ne (P : Packet) : (P.den:R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)

omit [CharZero R] in
theorem lower (P : Packet) (x y z w : R) : Matrix.IsLowerTriangular (A P x y z w) := by
  intro i j hij
  change i < j at hij
  simp [A,intA,rawMatrix,hij]

omit [CharZero R] in
theorem ev_eq {u v : V} (h : eqV u v = true) : ev x y z w u = ev x y z w v := by
  funext i
  rw [ev,ev,of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))]

omit [CharZero R] in
theorem ev_act (h : Roots P.red x y z w) (v : V) :
    ev x y z w (act P v) = mat (intA P x y z w) (ev x y z w v) := by
  ext i
  simp only [ev,act,eval_sum,eval_mul h,mat_apply,Matrix.mulVec_apply_eq_sum,intA]

omit [CharZero R] in
theorem ev_out (h : Roots P.red x y z w) (v : V) :
    val x y z w (out P v) = row (intB P x y z w) (ev x y z w v) := by
  simp only [out,eval_sum,eval_mul h,row_apply,dotProduct,intB,ev]

omit [CharZero R] in
theorem ev_mulV (h : Roots P.red x y z w) (u v : V) :
    ev x y z w (mulV P u v) = ev x y z w u * ev x y z w v := by
  ext i
  simp only [ev,mulV,eval_mul h,Pi.mul_apply]

omit [CharZero R] in
theorem ev_subV (u v : V) : ev x y z w (subV u v) = ev x y z w u - ev x y z w v := by
  ext i
  simp [ev,subV,val_add,val_sc,Pi.sub_apply,sub_eq_add_neg]

omit [CharZero R] in
theorem ev_scaleV (n : Nat) (v : V) : ev x y z w (scaleV n v) = (n:R) • ev x y z w v := by
  ext i
  simp [ev,scaleV,val_sc,Pi.smul_apply,smul_eq_mul]

omit [CharZero R] in
theorem intNodes (h : Roots P.red x y z w) (cert : Receipts P) :
    ev x y z w (node P) = nodes (intA P x y z w) := by
  have e : ev x y z w (act P one) = ev x y z w (node P) := ev_eq cert.node
  rw [ev_act h] at e
  have j : ev x y z w one = (1 : Fin 14 → R) := by ext i; simp [ev,one]
  rw [j] at e
  exact e.symm

omit [CharZero R] in
theorem nodes_scaled (h : Roots P.red x y z w) (cert : Receipts P) :
    nodes (A P x y z w) = ((P.den:R)⁻¹) • ev x y z w (node P) := by
  rw [intNodes h cert]
  exact Matrix.smul_mulVec _ _ _

omit [CharZero R] in
theorem ev_powC (h : Roots P.red x y z w) (d : Nat) :
    ev x y z w (powC P d) = (ev x y z w (node P))^d := by
  ext i
  simp only [ev,powC,eval_pow h,Pi.pow_apply]

omit [CharZero R] in
theorem scaled_powC (h : Roots P.red x y z w) (cert : Receipts P) (d : Nat) :
    (nodes (A P x y z w))^d = (((P.den:R)⁻¹)^d) • ev x y z w (powC P d) := by
  rw [nodes_scaled h cert,ev_powC h]
  ext i
  simp only [Pi.pow_apply,Pi.smul_apply,smul_eq_mul,mul_pow]

omit [CharZero R] in
def band (P : Packet) (x y z w : R) (d : Nat) : Submodule R (Fin 14 → R) :=
  Submodule.span R (Set.range (fun i => ev x y z w (gen P d i)))

omit [CharZero R] in
theorem combo_mem (h : Roots P.red x y z w) (d : Nat) (q : Nat → C16) :
    ev x y z w (combo P d q) ∈ band P x y z w d := by
  have hsum : ev x y z w (combo P d q) =
      ∑ j : Fin (P.size d), (val x y z w (q j.val)) • ev x y z w (gen P d j) := by
    ext i
    simp only [ev,combo,eval_sum,eval_mul h,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hsum]
  apply Submodule.sum_mem
  intro i _
  exact (band P x y z w d).smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)

theorem witnessed (h : Roots P.red x y z w) {d : Nat} {v : V} {q : Witness}
    (ok : checkCombo P d v q = true) : ev x y z w v ∈ band P x y z w d := by
  have e : ev x y z w (scaleV (q.scalePred+1) v) = ev x y z w (combo P d q.coefficients) := ev_eq ok
  rw [ev_scaleV] at e
  have u : IsUnit (((q.scalePred+1:Nat):R)) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
  apply ((band P x y z w d).smul_mem_iff_of_isUnit u).mp
  rw [e]
  exact combo_mem h _ _

omit [CharZero R] in
theorem span_mul_mem {X Y : Set (Fin 14 → R)} {L : Submodule R (Fin 14 → R)}
    (h : ∀ a ∈ X, ∀ b ∈ Y, a*b∈L)
    {a b : Fin 14 → R} (ha : a∈Submodule.span R X) (hb : b∈Submodule.span R Y) :
    a*b∈L := by
  have H : ∀ w∈Y, a*w∈L := by
    intro w hw
    have hin : Submodule.span R X ≤ L.comap (LinearMap.mulLeft R w) := by
      apply Submodule.span_le.mpr
      intro v hv
      change w*v∈L
      rw [mul_comm]
      exact h v hv w hw
    have z := hin ha
    change w*a∈L at z
    simpa [mul_comm] using z
  have hin : Submodule.span R Y ≤ L.comap (LinearMap.mulLeft R a) := by
    apply Submodule.span_le.mpr
    intro w hw
    exact H w hw
  exact hin hb

omit [CharZero R] in
theorem row_scaleL (r : R) (u v : Fin 14 → R) : row (r • u) v = r * row u v := by
  simp only [row_apply,smul_dotProduct,smul_eq_mul]

omit [CharZero R] in
theorem mat_scaleL (r : R) (m : Matrix (Fin 14) (Fin 14) R) (v : Fin 14 → R) :
    mat (r • m) v = r • mat m v := by
  rw [mat_apply,mat_apply,Matrix.smul_mulVec]

noncomputable def sufficient (h : Roots P.red x y z w) (cert : Receipts P) :
    SufficientFlags 11 (A P x y z w) (b P x y z w) := by
  refine {
    band := band P x y z w
    stepA := ?_
    stepC := ?_
    mulBand := ?_
    primitive := ?_
    silent := ?_
    scalar := ?_ }
  · intro d hd v hv
    have hin : band P x y z w d ≤ (band P x y z w (d+1)).comap (mat (A P x y z w)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have m := witnessed h (cert.stepA d (by omega) i)
      rw [ev_act h] at m
      have ms := (band P x y z w (d+1)).smul_mem ((P.den:R)⁻¹) m
      apply (Submodule.mem_comap).2
      simpa only [A,mat_scaleL] using ms
    exact hin hv
  · intro d hd v hv
    have hin : band P x y z w d ≤ (band P x y z w (d+1)).comap (diag (nodes (A P x y z w))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have m := witnessed h (cert.stepC d (by omega) i)
      rw [ev_mulV h] at m
      apply (Submodule.mem_comap).2
      change nodes (A P x y z w) * ev x y z w (gen P d i) ∈ band P x y z w (d+1)
      rw [nodes_scaled h cert,smul_mul_assoc]
      exact (band P x y z w (d+1)).smul_mem _ m
    exact hin hv
  · intro d e hd v t hv ht
    apply span_mul_mem _ hv ht
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    have m := witnessed h (cert.product d e hd i j)
    rwa [ev_mulV h] at m
  · intro d hd
    have m := witnessed h (cert.primitive d (by omega))
    simp only [primitiveV,ev_subV,ev_scaleV,ev_act h] at m
    have ms := (band P x y z w (d+1)).smul_mem (((P.den:R)⁻¹)^(d+1)) m
    have ee : ((d+1:Nat):R) • mat (A P x y z w) (nodes (A P x y z w)^d) -
        nodes (A P x y z w)^(d+1) = (((P.den:R)⁻¹)^(d+1)) •
        (((d+1:Nat):R) • mat (intA P x y z w) (ev x y z w (powC P d)) -
          ev x y z w (powC P (d+1))) := by
      rw [scaled_powC h cert d,scaled_powC h cert (d+1)]
      simp only [A,mat_apply,Matrix.smul_mulVec,Matrix.mulVec_smul]
      rw [pow_succ,smul_sub]
      module
    rw [ee]
    exact ms
  · intro d hd v hv
    have hin : band P x y z w d ≤ (row (b P x y z w)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have e := congrArg (val x y z w) (of_decide_eq_true (cert.silent d hd i))
      rw [ev_out h,val_pack,Int.cast_zero] at e
      change row (b P x y z w) (ev x y z w (gen P d i))=0
      rw [b,row_scaleL,e,mul_zero]
    exact hin hv
  · intro d hd
    have e := congrArg (val x y z w) (of_decide_eq_true (cert.scalar d hd))
    simp only [val_sc,ev_out h,val_pack,Int.cast_natCast,Int.cast_pow] at e
    rw [scaled_powC h cert d]
    rw [b,row_scaleL,map_smul,smul_eq_mul]
    have key : ((P.den:R)⁻¹)*((P.den:R)⁻¹)^d * ((P.den:R)^(d+1))=1 := by
      rw [←pow_succ',←mul_pow, inv_mul_cancel₀ (den_ne P),one_pow]
    rw [←key,←e]
    ring

theorem order_eleven (h : Roots P.red x y z w) (cert : Receipts P) :
    HasOrder 11 (A P x y z w) (b P x y z w) :=
  (sufficient h cert).hasOrder

/-- Root with four leaf children and one seven-vertex bush child. -/
def nextTree : FiniteRootedTree := (.leaf ◂ clockTree 6).addBush 4

theorem next_order : (nextTree.order:Nat)=12 := by decide
theorem next_factorial : (nextTree.factorial:Nat)=84 := by decide

omit [CharZero R] in
theorem next_phi (M : Matrix (Fin 14) (Fin 14) R) : Φ nextTree M =
    nodes M^4 * mat M (nodes M^6) := by
  ext i
  simp only [nextTree,Φ_addBush,Φ,Pi.mul_apply,one_mul,mat_apply]
  have e : Φ (clockTree 6) M = nodes M^6 := by
    ext j
    simp [clockTree,nodes]
    ring
  rw [e]
  exact mul_comm _ _

theorem no_order_twelve (h : Roots P.red x y z w) (cert : Receipts P) :
    ¬ HasOrder 12 (A P x y z w) (b P x y z w) := by
  intro ho
  have paid := ho nextTree next_order.le
  rw [next_factorial,next_phi,←row_apply] at paid
  have eval : val x y z w (failureNumerator P) =
      84 * row (intB P x y z w)
        (ev x y z w (powC P 4) * mat (intA P x y z w) (ev x y z w (powC P 6))) - (P.den:R)^12 := by
    simp only [failureNumerator,val_add,val_sc,ev_out h,ev_mulV h,ev_act h,val_pack,
      Int.cast_neg,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat,sub_eq_add_neg]
  have ps : ((P.den:R)⁻¹)^12 * (val x y z w (failureNumerator P)) = 0 := by
    rw [scaled_powC h cert 4,scaled_powC h cert 6] at paid
    rw [A,mat_scaleL,map_smul] at paid
    simp only [smul_mul_assoc,mul_smul_comm] at paid
    rw [b,row_scaleL] at paid
    simp only [map_smul,smul_eq_mul] at paid
    rw [eval]
    have hh : ((P.den:R)⁻¹)^12 * (P.den:R)^12 = 1 := by
      rw [←mul_pow,inv_mul_cancel₀ (den_ne P),one_pow]
    rw [mul_sub,hh]
    apply sub_eq_zero.mpr
    convert paid using 1 <;> push_cast <;> ring
  have zero : val x y z w (failureNumerator P)=0 :=
    (mul_eq_zero.mp ps).resolve_left (pow_ne_zero 12 (inv_ne_zero (den_ne P)))
  have e := congrArg (val x y z w) (of_decide_eq_true cert.failure)
  rw [eval_mul h,zero,zero_mul,val_pack,Int.cast_natCast] at e
  exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero P.failureDenPred)) e.symm

end Generic
end RKResearch.Certified.DIRK11Width14IntegerCore
