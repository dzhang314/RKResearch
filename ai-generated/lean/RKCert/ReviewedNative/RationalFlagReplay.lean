module

public import RKCert.ReviewedNative.SufficientGradedFlags
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! # Exact finite sufficient flags for literal rational tableaux

Pivot-coordinate projection just supplies coefficients in a given span.
A separately kernel-checked equality verifies a proposed projection;
completeness or independence of the supplied basis is never assumed. -/

namespace RKResearch.Certified.RationalFlagReplay

open RKResearch Graded
open scoped Matrix BigOperators

variable {s : ℕ}
abbrev V (s : ℕ) := Fin s → ℚ

structure Packet (s : ℕ) where
  a : Fin s → Fin s → ℚ
  b : V s
  clock : V s
  size : ℕ → ℕ
  pivot : (d : ℕ) → Fin (size d) → Fin s
  basis : (d : ℕ) → Fin (size d) → V s

def matrix (P : Packet s) : Matrix (Fin s) (Fin s) ℚ :=
  fun i j => if i < j then 0 else P.a i j

theorem lower (P : Packet s) : Matrix.IsLowerTriangular (matrix P) := by
  intro i j hij
  change i < j at hij
  simp [matrix, hij]

/-- Finite sums separated from typeclass-driven elaboration in the
closed kernel checks. -/
def sumFin : {n : ℕ} → (Fin n → ℚ) → ℚ
  | 0, _ => 0
  | n+1, f => f 0 + sumFin (fun j : Fin n => f j.succ)

theorem sumFin_eq {n : ℕ} (f : Fin n → ℚ) : sumFin f = ∑ j, f j := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp only [sumFin,ih,Fin.sum_univ_succ]

def act (P : Packet s) (v : V s) : V s :=
  fun i => sumFin fun j => matrix P i j * v j

def output (P : Packet s) (v : V s) : ℚ := sumFin fun j => P.b j * v j

theorem act_eq (P : Packet s) (v : V s) : act P v = mat (matrix P) v := by
  funext i
  simp only [act,sumFin_eq,mat_apply,Matrix.mulVec_apply_eq_sum]

theorem output_eq (P : Packet s) (v : V s) : output P v = row P.b v := by
  simp only [output,sumFin_eq,row_apply,dotProduct]

def project (P : Packet s) (d : ℕ) (v : V s) : V s :=
  fun i => sumFin fun j : Fin (P.size d) => v (P.pivot d j) * P.basis d j i

def eqV (v w : V s) : Bool := (List.finRange s).all fun i => decide (v i = w i)

theorem eq_of_eqV {v w : V s} (h : eqV v w = true) : v=w :=
  funext fun i => of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

def checkNode (P : Packet s) : Bool := eqV (act P 1) P.clock

def checkA (P : Packet s) (d : ℕ) (i : Fin (P.size d)) : Bool :=
  let v := act P (P.basis d i)
  eqV v (project P (d+1) v)

def checkC (P : Packet s) (d : ℕ) (i : Fin (P.size d)) : Bool :=
  let v := P.clock * P.basis d i
  eqV v (project P (d+1) v)

def checkProduct (P : Packet s) (d e : ℕ) (i : Fin (P.size d)) (j : Fin (P.size e)) : Bool :=
  let v := P.basis d i * P.basis e j
  eqV v (project P (d+e) v)

def checkPrimitive (P : Packet s) (d : ℕ) : Bool :=
  let v := ((d+1 : ℕ) : ℚ) • act P (P.clock^d) - P.clock^(d+1)
  eqV v (project P (d+1) v)

def checkSilent (P : Packet s) (d : ℕ) (i : Fin (P.size d)) : Bool :=
  decide (output P (P.basis d i) = 0)

def checkScalar (P : Packet s) (d : ℕ) : Bool :=
  decide (((d+1 : ℕ) : ℚ) * output P (P.clock^d) = 1)

def bushResidual (P : Packet s) (d : ℕ) : ℚ :=
  ((d+1 : ℕ) : ℚ) * output P (P.clock^d) - 1

structure Receipts (p : ℕ) (P : Packet s) : Prop where
  node : checkNode P = true
  stepA : ∀ d, d+1<p → ∀ i, checkA P d i = true
  stepC : ∀ d, d+1<p → ∀ i, checkC P d i = true
  product : ∀ d e, d+e<p → ∀ i j, checkProduct P d e i j = true
  primitive : ∀ d, d+1<p → checkPrimitive P d = true
  silent : ∀ d, d<p → ∀ i, checkSilent P d i = true
  scalar : ∀ d, d<p → checkScalar P d = true

variable {p : ℕ} {P : Packet s}

theorem node_eq (h : Receipts p P) : P.clock = nodes (matrix P) := by
  have e := eq_of_eqV h.node
  rw [act_eq] at e
  exact e.symm

def band (P : Packet s) (d : ℕ) : Submodule ℚ (V s) :=
  Submodule.span ℚ (Set.range (P.basis d))

theorem project_mem (P : Packet s) (d : ℕ) (v : V s) :
    project P d v ∈ band P d := by
  have eq : project P d v =
      ∑ j : Fin (P.size d), v (P.pivot d j) • P.basis d j := by
    ext i
    simp only [project,sumFin_eq,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [eq]
  exact Submodule.sum_mem _ fun j _ =>
    (band P d).smul_mem _ (Submodule.subset_span ⟨j,rfl⟩)

theorem span_mul_mem {X Y : Set (V s)} {U : Submodule ℚ (V s)}
    (h : ∀ a ∈ X, ∀ b ∈ Y, a*b∈U)
    {a b : V s} (ha : a ∈ Submodule.span ℚ X) (hb : b ∈ Submodule.span ℚ Y) :
    a*b ∈ U := by
  have H : ∀ w ∈ Y, a*w ∈ U := by
    intro w hw
    have hin : Submodule.span ℚ X ≤ U.comap (LinearMap.mulLeft ℚ w) := by
      apply Submodule.span_le.mpr
      intro v hv
      change w*v ∈ U
      rw [mul_comm]
      exact h v hv w hw
    have z := hin ha
    change w*a ∈ U at z
    simpa [mul_comm] using z
  have hin : Submodule.span ℚ Y ≤ U.comap (LinearMap.mulLeft ℚ a) :=
    Submodule.span_le.mpr H
  exact hin hb

noncomputable def sufficient (h : Receipts p P) :
    SufficientFlags p (matrix P) P.b := by
  refine ⟨band P,?_,?_,?_,?_,?_,?_⟩
  · intro d hd v hv
    have hin : band P d ≤ (band P (d+1)).comap (mat (matrix P)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have e := eq_of_eqV (h.stepA d hd i)
      change act P (P.basis d i) = project P (d+1) (act P (P.basis d i)) at e
      rw [act_eq] at e
      change mat (matrix P) (P.basis d i) ∈ band P (d+1)
      rw [e]
      exact project_mem _ _ _
    exact hin hv
  · intro d hd v hv
    have hin : band P d ≤ (band P (d+1)).comap (diag (nodes (matrix P))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have e := eq_of_eqV (h.stepC d hd i)
      change P.clock * P.basis d i = project P (d+1) (P.clock * P.basis d i) at e
      rw [node_eq h] at e
      change nodes (matrix P) * P.basis d i ∈ band P (d+1)
      rw [e]
      exact project_mem _ _ _
    exact hin hv
  · intro d e hd a b ha hb
    apply span_mul_mem _ ha hb
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    have eq := eq_of_eqV (h.product d e hd i j)
    change P.basis d i * P.basis e j = project P (d+e) (P.basis d i * P.basis e j) at eq
    rw [eq]
    exact project_mem _ _ _
  · intro d hd
    have eq := eq_of_eqV (h.primitive d hd)
    change ((d+1 : ℕ) : ℚ) • act P (P.clock^d) - P.clock^(d+1) =
      project P (d+1) (((d+1 : ℕ) : ℚ) • act P (P.clock^d) - P.clock^(d+1)) at eq
    rw [act_eq,node_eq h] at eq
    rw [eq]
    exact project_mem _ _ _
  · intro d hd v hv
    have hin : band P d ≤ (row P.b).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have eq : output P (P.basis d i) = 0 := of_decide_eq_true (h.silent d hd i)
      rwa [output_eq] at eq
    exact hin hv
  · intro d hd
    have eq : ((d+1 : ℕ) : ℚ) * output P (P.clock^d) = 1 := of_decide_eq_true (h.scalar d hd)
    rwa [output_eq,node_eq h] at eq

theorem order (h : Receipts p P) : HasOrder p (matrix P) P.b :=
  (sufficient h).hasOrder

theorem no_order_succ (h : Receipts p P) (bad : bushResidual P p ≠ 0) :
    ¬ HasOrder (p+1) (matrix P) P.b := by
  intro ho
  apply bad
  have hm := ho.hasQuadratureOrder p (by omega)
  unfold bushResidual
  rw [output_eq,node_eq h,row_apply]
  exact sub_eq_zero.mpr hm

end RKResearch.Certified.RationalFlagReplay
