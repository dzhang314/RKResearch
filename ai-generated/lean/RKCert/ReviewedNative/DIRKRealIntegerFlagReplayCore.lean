module

public import RKCert.ReviewedNative.SufficientGradedFlags
public import RKCert.ReviewedNative.CubicCubicQuadraticFractionReplay
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! Computational receipts for explicit bases of sufficient grades.
Small kernel-checked coordinate comparisons certify the span closures;
they do not trust a numerical rank solve or a compiler reduction. -/
namespace RKResearch.Certified.DIRKRealIntegerFlagReplay
open RKResearch FiniteRootedTree Graded CubicCubicQuadraticFractionReplay
open CubicCubicQuadraticReplay (Reductions)
open scoped Matrix BigOperators

structure Packet where
  red : Reductions
  a : Nat → Nat → C18
  b : Nat → C18
  clock : Nat → C18
  size : Nat → Nat
  basis : Nat → Nat → Nat → C18
  nextA : Nat → Nat → Nat → C18
  nextC : Nat → Nat → Nat → C18
  product : Nat → Nat → Nat → Nat → Nat → C18
  primitive : Nat → Nat → C18
  bushInverse : C18

abbrev V := Fin 11 → C18

def smul (D : Reductions) (x y : C18) : C18 :=
  if x = pack 0 then pack 0
  else if y = pack 0 then pack 0
  else if x = pack 1 then y
  else if y = pack 1 then x
  else mul D x y

def csum : {n : Nat} → (Fin n → C18) → C18
  | 0, _ => pack 0
  | n+1, f => add (f 0) (csum (fun j : Fin n => f j.succ))

def power (D : Reductions) (x : C18) : Nat → C18
  | 0 => pack 1
  | n+1 => smul D (power D x n) x

def rawMatrix (P : Packet) (i j : Fin 11) : C18 :=
  if i < j then pack 0 else P.a i.val j.val
def rawBeta (P : Packet) : V := fun i => P.b i.val
def node (P : Packet) : V := fun i => P.clock i.val
def one : V := fun _ => pack 1
def powC (P : Packet) (j : Nat) : V := fun i => power P.red (node P i) j
def gen (P : Packet) (d : Nat) (i : Fin (P.size d)) : V := fun j => P.basis d i.val j.val

def subV (P : Packet) (u v : V) : V :=
  fun i => add (u i) (smul P.red (pack (-1)) (v i))
def mulV (P : Packet) (u v : V) : V := fun i => smul P.red (u i) (v i)
def scaleV (P : Packet) (n : Nat) (u : V) : V :=
  fun i => smul P.red (pack (n:Int)) (u i)
def act (P : Packet) (v : V) : V :=
  fun i => csum fun j => smul P.red (rawMatrix P i j) (v j)
def out (P : Packet) (v : V) : C18 :=
  csum fun j => smul P.red (rawBeta P j) (v j)
def combo (P : Packet) (d : Nat) (c : Nat → C18) : V :=
  fun i => csum fun j : Fin (P.size d) => smul P.red (c j.val) (gen P d j i)

def eqV (v w : V) : Bool :=
  (List.finRange 11).all fun i => eqf (v i) (w i)

def checkNode (P : Packet) : Bool := eqV (act P one) (node P)
def checkA (P : Packet) (d : Nat) (i : Fin (P.size d)) : Bool :=
  eqV (act P (gen P d i)) (combo P (d+1) (P.nextA d i.val))
def checkC (P : Packet) (d : Nat) (i : Fin (P.size d)) : Bool :=
  eqV (mulV P (node P) (gen P d i)) (combo P (d+1) (P.nextC d i.val))
def checkProduct (P : Packet) (d e : Nat) (i : Fin (P.size d)) (j : Fin (P.size e)) : Bool :=
  eqV (mulV P (gen P d i) (gen P e j)) (combo P (d+e) (P.product d e i.val j.val))
def checkPrimitive (P : Packet) (d : Nat) : Bool :=
  eqV (subV P (scaleV P (d+1) (act P (powC P d))) (powC P (d+1)))
    (combo P (d+1) (P.primitive d))
def checkSilent (P : Packet) (d : Nat) (i : Fin (P.size d)) : Bool :=
  eqf (out P (gen P d i)) (pack 0)
def checkScalar (P : Packet) (d : Nat) : Bool :=
  eqf (smul P.red (pack ((d+1 : Nat) : Int)) (out P (powC P d))) (pack 1)
def bushResidual (P : Packet) : C18 :=
  add (smul P.red (pack 11) (out P (powC P 10))) (pack (-1))
def checkBush (P : Packet) : Bool :=
  eqf (smul P.red (bushResidual P) P.bushInverse) (pack 1)

structure Receipts (P : Packet) : Prop where
  node : checkNode P = true
  stepA : ∀ d < 9, ∀ i, checkA P d i = true
  stepC : ∀ d < 9, ∀ i, checkC P d i = true
  product : ∀ d e, d+e < 10 → ∀ i j, checkProduct P d e i j = true
  primitive : ∀ d < 9, checkPrimitive P d = true
  silent : ∀ d < 10, ∀ i, checkSilent P d i = true
  scalar : ∀ d < 10, checkScalar P d = true
  bush : checkBush P = true

section Generic

variable {R : Type*} [Field R] [CharZero R]
variable {P : Packet} {x y z : R}

theorem eval_mul (h : Roots P.red x y z) (u v : C18) :
    val x y z (smul P.red u v) = val x y z u * val x y z v := by
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

theorem eval_sum {n : Nat} (f : Fin n → C18) :
    val x y z (csum f) = ∑ i, val x y z (f i) := by
  induction n with
  | zero => simp [csum]
  | succ n ih => simp only [csum,val_add,ih,Fin.sum_univ_succ]

theorem eval_pow (h : Roots P.red x y z) (u : C18) (n : Nat) :
    val x y z (power P.red u n) = (val x y z u)^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp only [power,eval_mul h,ih,pow_succ]

def ev (x y z : R) (v : V) : Fin 11 → R := fun i => val x y z (v i)
def A (P : Packet) (x y z : R) : Matrix (Fin 11) (Fin 11) R :=
  fun i j => val x y z (rawMatrix P i j)
def b (P : Packet) (x y z : R) : Fin 11 → R := ev x y z (rawBeta P)

theorem lower (P : Packet) (x y z : R) : Matrix.IsLowerTriangular (A P x y z) := by
  intro i j hij
  change i < j at hij
  simp [A,rawMatrix,hij]

theorem ev_eq {u v : V} (h : eqV u v = true) : ev x y z u = ev x y z v := by
  funext i
  exact val_eqf (List.all_eq_true.mp h i (List.mem_finRange i))

theorem ev_act (h : Roots P.red x y z) (v : V) :
    ev x y z (act P v) = mat (A P x y z) (ev x y z v) := by
  ext i
  simp only [ev,act,eval_sum,eval_mul h,mat_apply,Matrix.mulVec_apply_eq_sum,A]

theorem ev_out (h : Roots P.red x y z) (v : V) :
    val x y z (out P v) = row (b P x y z) (ev x y z v) := by
  simp only [out,eval_sum,eval_mul h,row_apply,dotProduct,b,ev]

theorem ev_mulV (h : Roots P.red x y z) (v w : V) :
    ev x y z (mulV P v w) = ev x y z v * ev x y z w := by
  ext i
  simp only [ev,mulV,eval_mul h,Pi.mul_apply]

theorem ev_subV (h : Roots P.red x y z) (v w : V) :
    ev x y z (subV P v w) = ev x y z v - ev x y z w := by
  ext i
  simp [ev,subV,val_add,eval_mul h,Pi.sub_apply,sub_eq_add_neg]

theorem ev_scaleV (h : Roots P.red x y z) (v : V) (n : Nat) :
    ev x y z (scaleV P n v) = (n:R) • ev x y z v := by
  ext i
  simp [ev,scaleV,eval_mul h,Pi.smul_apply,smul_eq_mul]

theorem ev_nodes (h : Roots P.red x y z) (cert : Receipts P) :
    ev x y z (node P) = nodes (A P x y z) := by
  have e : ev x y z (act P one) = ev x y z (node P) := ev_eq cert.node
  rw [ev_act h] at e
  have j : ev x y z one = (1 : Fin 11 → R) := by ext i; simp [ev,one]
  rw [j] at e
  exact e.symm

theorem ev_powC (h : Roots P.red x y z) (cert : Receipts P) (d : Nat) :
    ev x y z (powC P d) = (nodes (A P x y z))^d := by
  rw [←ev_nodes h cert]
  ext i
  simp only [ev,powC,eval_pow h,Pi.pow_apply]

def band (P : Packet) (x y z : R) (d : Nat) : Submodule R (Fin 11 → R) :=
  Submodule.span R (Set.range (fun i => ev x y z (gen P d i)))

theorem combo_mem (h : Roots P.red x y z) (d : Nat) (q : Nat → C18) :
    ev x y z (combo P d q) ∈ band P x y z d := by
  have hsum : ev x y z (combo P d q) =
      ∑ j : Fin (P.size d), (val x y z (q j.val)) • ev x y z (gen P d j) := by
    ext i
    simp only [ev,combo,eval_sum,eval_mul h,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hsum]
  apply Submodule.sum_mem
  intro i _
  exact (band P x y z d).smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)

omit [CharZero R] in
theorem span_mul_mem {X Y : Set (Fin 11 → R)} {L : Submodule R (Fin 11 → R)}
    (h : ∀ a ∈ X, ∀ b ∈ Y, a*b∈L)
    {a b : Fin 11 → R} (ha : a∈Submodule.span R X) (hb : b∈Submodule.span R Y) :
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

noncomputable def sufficient (h : Roots P.red x y z) (cert : Receipts P) :
    SufficientFlags 10 (A P x y z) (b P x y z) := by
  refine {
    band := band P x y z
    stepA := ?_
    stepC := ?_
    mulBand := ?_
    primitive := ?_
    silent := ?_
    scalar := ?_ }
  · intro d hd v hv
    have hin : band P x y z d ≤ (band P x y z (d+1)).comap (mat (A P x y z)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have e : ev x y z (act P (gen P d i)) =
          ev x y z (combo P (d+1) (P.nextA d i.val)) := ev_eq (cert.stepA d (by omega) i)
      rw [ev_act h] at e
      change mat (A P x y z) (ev x y z (gen P d i)) ∈ band P x y z (d+1)
      rw [e]
      exact combo_mem h _ _
    exact hin hv
  · intro d hd v hv
    have hin : band P x y z d ≤ (band P x y z (d+1)).comap (diag (nodes (A P x y z))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have e : ev x y z (mulV P (node P) (gen P d i)) =
          ev x y z (combo P (d+1) (P.nextC d i.val)) := ev_eq (cert.stepC d (by omega) i)
      rw [ev_mulV h,ev_nodes h cert] at e
      change nodes (A P x y z)*ev x y z (gen P d i) ∈ band P x y z (d+1)
      rw [e]
      exact combo_mem h _ _
    exact hin hv
  · intro d e hd v w hv hw
    apply span_mul_mem _ hv hw
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    have z' : ev x y z (mulV P (gen P d i) (gen P e j)) =
        ev x y z (combo P (d+e) (P.product d e i.val j.val)) :=
      ev_eq (cert.product d e hd i j)
    rw [ev_mulV h] at z'
    rw [z']
    exact combo_mem h _ _
  · intro d hd
    have z' : ev x y z (subV P (scaleV P (d+1) (act P (powC P d))) (powC P (d+1))) =
        ev x y z (combo P (d+1) (P.primitive d)) := ev_eq (cert.primitive d (by omega))
    rw [ev_subV h,ev_scaleV h,ev_act h,ev_powC h cert,ev_powC h cert] at z'
    rw [z']
    exact combo_mem h _ _
  · intro d hd v hv
    have hin : band P x y z d ≤ (row (b P x y z)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have e : val x y z (out P (gen P d i))=val x y z (pack 0) := val_eqf (cert.silent d hd i)
      rw [ev_out h,val_pack,Int.cast_zero] at e
      exact e
    exact hin hv
  · intro d hd
    have e : val x y z (smul P.red (pack ((d+1 : Nat):Int)) (out P (powC P d))) =
        val x y z (pack 1) := val_eqf (cert.scalar d hd)
    rw [eval_mul h,val_pack,val_pack,Int.cast_one,Int.cast_natCast,ev_out h,ev_powC h cert] at e
    exact e

theorem order_ten (h : Roots P.red x y z) (cert : Receipts P) :
    HasOrder 10 (A P x y z) (b P x y z) :=
  (sufficient h cert).hasOrder

theorem no_order_eleven [Nontrivial R] (h : Roots P.red x y z) (cert : Receipts P) :
    ¬ HasOrder 11 (A P x y z) (b P x y z) := by
  intro ho
  have hm := ho.hasQuadratureOrder 10 (by decide)
  have bres : val x y z (bushResidual P) = 0 := by
    unfold bushResidual
    rw [val_add,eval_mul h,ev_out h,ev_powC h cert,val_pack,val_pack]
    simp only [Int.cast_ofNat,Int.cast_neg,Int.cast_one,row_apply]
    simpa [show (10:Nat).succ=11 by decide, hm] using
      (show (11:R) * (b P x y z ⬝ᵥ nodes (A P x y z)^10) + -1 = 0 by
        rw [show (11:R) * (b P x y z ⬝ᵥ nodes (A P x y z)^10)=1 from hm]
        simp)
  have p : val x y z (smul P.red (bushResidual P) P.bushInverse) = val x y z (pack 1) := val_eqf cert.bush
  rw [eval_mul h,bres,zero_mul,val_pack,Int.cast_one] at p
  exact zero_ne_one p

end Generic
end RKResearch.Certified.DIRKRealIntegerFlagReplay

#print axioms RKResearch.Certified.DIRKRealIntegerFlagReplay.order_ten
