module

public import RKCert.ReviewedNative.DualSupport12
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! A literal compact vector interface to the complementary-support proof.
No rank or basis independence is required: each proposed linear
combination is independently checked. -/
namespace RKResearch.Certified.DualSupport12VectorReplay

open RKResearch Graded FiniteRootedTree
open scoped Matrix BigOperators FiniteRootedTree

variable {R : Type*} [CommRing R]

abbrev V (R : Type*) := Fin 15 → R
abbrev EqV (u v : V R) : Prop := ∀ i, u i = v i

structure Packet (R : Type*) where
  a : Fin 15 → Fin 15 → R
  b : V R
  c : V R
  genF : Nat → V R
  genB : Nat → V R
  coeff : Nat → Nat → Nat → Nat → R
  starInverse : R
  diagInverse : R

abbrev ghost (i : Fin 15) : Prop := 1 ≤ i.val ∧ i.val ≤ 4

def width (d : Nat) : Nat := min 3 (d-2)

def csum : {n : Nat} → (Fin n → R) → R
  | 0, _ => 0
  | n+1, f => f 0 + csum (fun j : Fin n => f j.succ)

theorem csum_eq {n : Nat} (f : Fin n → R) : csum f = ∑ j, f j := by
  induction n with
  | zero => simp [csum]
  | succ n ih => simp only [csum, ih, Fin.sum_univ_succ]

def matrix (P : Packet R) : Matrix (Fin 15) (Fin 15) R :=
  fun i j => if i < j then 0 else P.a i j

theorem lower (P : Packet R) : Matrix.IsLowerTriangular (matrix P) := by
  intro i j hij
  change i < j at hij
  simp [matrix, hij]

def action (M : Matrix (Fin 15) (Fin 15) R) (v : V R) : V R :=
  fun i => csum fun j => M i j * v j

def pair (u v : V R) : R := csum fun j => u j * v j

theorem action_eq (M : Matrix (Fin 15) (Fin 15) R) (v : V R) :
    action M v = mat M v := by
  ext i
  simp only [action, csum_eq, mat_apply, Matrix.mulVec_apply_eq_sum]

theorem pair_eq (u v : V R) : pair u v = row u v := by
  simp [pair, csum_eq, dotProduct]

def A0 (P : Packet R) := action (matrix P)
def N0 (P : Packet R) := action (matrix P).transpose
def Y (P : Packet R) : V R := 1-P.c
def W (P : Packet R) (d : Nat) : V R := P.b * (Y P)^d
def F (P : Packet R) (d : Nat) : V R :=
  ((d+1 : Nat) : R) • A0 P (P.c^d) - P.c^(d+1)
def B (P : Packet R) (d : Nat) : V R :=
  ((d+1 : Nat) : R) • N0 P (W P d) - W P (d+1)

def combo (P : Packet R) (g : Nat → V R) (d op i : Nat) : V R :=
  fun j => csum fun s : Fin (width (d+1)) => P.coeff op d i s.val * g s.val j

def nextDefect (P : Packet R) : R := 13 * pair P.b (P.c^12) - 1

structure Receipts (P : Packet R) : Prop where
  nodes : EqV (A0 P 1) P.c
  ghosts : ∀ i, ghost i → P.b i = 0
  fSupport : ∀ k : Fin 3, ∀ i, ¬ ghost i → P.genF k.val i = 0
  bSupport : ∀ k : Fin 3, ∀ i, ghost i → P.genB k.val i = 0
  fA : ∀ d < 5, ∀ k : Fin (width d), EqV (A0 P (P.genF k.val)) (combo P P.genF d 0 k.val)
  fC : ∀ d < 5, ∀ k : Fin (width d), EqV (P.c * P.genF k.val) (combo P P.genF d 1 k.val)
  fP : ∀ d < 5, EqV (F P d) (combo P P.genF d 2 0)
  bA : ∀ d < 5, ∀ k : Fin (width d), EqV (N0 P (P.genB k.val)) (combo P P.genB d 3 k.val)
  bY : ∀ d < 5, ∀ k : Fin (width d), EqV (Y P * P.genB k.val) (combo P P.genB d 4 k.val)
  bP : ∀ d < 5, EqV (B P d) (combo P P.genB d 5 0)
  bSilent : ∀ d ≤ 5, ∀ j, d+j < 12 → ∀ k : Fin (width d), pair (P.genB k.val) (P.c^j) = 0
  fASilent : ∀ k i : Fin 3, pair (P.genB i.val) (A0 P (P.genF k.val)) = 0
  fAMoment : ∀ k : Fin 3, ∀ j : Fin 6, pair (W P j.val) (A0 P (P.genF k.val)) = 0
  fPSilent : ∀ i : Fin 3, pair (P.genB i.val) (F P 5) = 0
  fPMoment : ∀ j : Fin 6, pair (W P j.val) (F P 5) = 0
  scalar : ∀ j < 12, ((j+1 : Nat) : R) * pair P.b (P.c^j) = 1
  nextUnit : nextDefect P * P.starInverse = 1
  diagUnit : matrix P 1 1 * P.diagInverse = 1
  firstDiag : matrix P 0 0 = 0

variable {P : Packet R} (cert : Receipts P)

include cert in
theorem node_eq : P.c = nodes (matrix P) := by
  have e := funext cert.nodes
  rw [A0, action_eq] at e
  exact e.symm

include cert in
theorem reflected_eq : Y P = DualSupport12.reflected (matrix P) := by
  rw [Y, DualSupport12.reflected, node_eq cert]

include cert in
theorem W_eq (k : Nat) : W P k = DualSupport12.moment (matrix P) P.b k := by
  rw [W, DualSupport12.moment, reflected_eq cert]

include cert in
theorem F_eq (d : Nat) : F P d = DualSupport12.forward (matrix P) d := by
  rw [F,A0,action_eq,node_eq cert,DualSupport12.forward]

include cert in
theorem B_eq (d : Nat) : B P d = DualSupport12.reverse (matrix P) P.b d := by
  rw [B,N0,action_eq,W_eq cert,W_eq cert,DualSupport12.reverse]

def band (gen : Nat → V R) (d : Nat) : Submodule R (V R) :=
  Submodule.span R (Set.range (fun j : Fin (width d) => gen j.val))

theorem span_gen {gen : Nat → V R} {d : Nat} (i : Fin (width d)) :
    gen i.val ∈ band gen d := Submodule.subset_span ⟨i,rfl⟩

theorem band_mono (gen : Nat → V R) (d : Nat) :
    band gen d ≤ band gen (d+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have e : width d ≤ width (d+1) := by unfold width; omega
  exact span_gen (⟨i.val, i.isLt.trans_le e⟩ : Fin (width (d+1)))

theorem combo_mem (gen : Nat → V R) (d op i : Nat) :
    combo P gen d op i ∈ band gen (d+1) := by
  have e : combo P gen d op i =
      ∑ j : Fin (width (d+1)), P.coeff op d i j.val • gen j.val := by
    ext k
    simp only [combo, csum_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact Submodule.sum_mem _ fun j _ => (band gen (d+1)).smul_mem _ (span_gen j)

theorem span_by_linear (gen : Nat → V R) (d : Nat) {M : V R →ₗ[R] V R}
    {S : Submodule R (V R)} (hs : ∀ j : Fin (width d), M (gen j.val) ∈ S) :
    ∀ v ∈ band gen d, M v ∈ S := by
  have a : band gen d ≤ S.comap M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hs i
  intro v hv
  exact a hv

theorem span_by_zero (gen : Nat → V R) (d : Nat) {M : V R →ₗ[R] R}
    (hs : ∀ j : Fin (width d), M (gen j.val) = 0) :
    ∀ v ∈ band gen d, M v = 0 := by
  have a : band gen d ≤ LinearMap.ker M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hs i
  intro v hv
  exact a hv

theorem f_supported
    (cert : Receipts P) (d : Nat) :
    ∀ v ∈ band P.genF d, DualSupport12.supported ghost v := by
  intro v hv i hi
  exact span_by_zero P.genF d (M:=LinearMap.proj i) (fun j =>
    cert.fSupport ⟨j.val,j.isLt.trans_le (Nat.min_le_left ..)⟩ i hi) v hv

theorem b_supported
    (cert : Receipts P) (d : Nat) :
    ∀ v ∈ band P.genB d, DualSupport12.zeroAt ghost v := by
  intro v hv i hi
  exact span_by_zero P.genB d (M:=LinearMap.proj i) (fun j =>
    cert.bSupport ⟨j.val,j.isLt.trans_le (Nat.min_le_left ..)⟩ i hi) v hv

theorem checked_high (cert : Receipts P) (v : V R)
    (bSilent : ∀ i : Fin 3, pair (P.genB i.val) v = 0)
    (bMoment : ∀ j : Fin 6, pair (W P j.val) v = 0) :
    v ∈ DualSupport12.high (matrix P) P.b (band P.genB) 5 := by
  apply DualSupport12.mem_high.mpr
  refine ⟨fun w hw => ?_, fun j hj => ?_⟩
  · rw [row_apply, dotProduct_comm, ← row_apply]
    exact span_by_zero P.genB 5 (M:=row v) (fun i => by
      rw [row_apply, dotProduct_comm, ← row_apply, ← pair_eq]
      exact bSilent ⟨i.val,i.isLt.trans_le (Nat.min_le_left ..)⟩) w hw
  · rw [← W_eq cert, ← pair_eq]
    exact bMoment ⟨j,by omega⟩

noncomputable def lowChecks (cert : Receipts P)
    (units : ∀ j < 5, IsUnit (((j+1 : Nat) : R))) :
    DualSupport12.LowChecks (matrix P) P.b where
  ghost := ghost
  fw := band P.genF
  bw := band P.genB
  weight_zero := cert.ghosts
  fw_zero := by
    intro d hd
    have e : width d = 0 := by unfold width; omega
    simp [band, e]
  fw_support := fun d _ => f_supported cert d
  bw_support := fun d _ => b_supported cert d
  bw_mono := fun d _ => band_mono P.genB d
  fw_A := by
    intro d hd
    apply span_by_linear (M:=mat (matrix P))
    intro j
    have e := funext (cert.fA d hd j)
    rw [A0,action_eq] at e
    rw [e]
    exact combo_mem P.genF d 0 j.val
  fw_C := by
    intro d hd
    apply span_by_linear (M:=diag (nodes (matrix P)))
    intro j
    have e := funext (cert.fC d hd j)
    rw [node_eq cert] at e
    change nodes (matrix P) * P.genF j.val ∈ _
    rw [e]
    exact combo_mem P.genF d 1 j.val
  fw_primitive := by
    intro d hd
    rw [← F_eq cert, funext (cert.fP d hd)]
    exact combo_mem P.genF d 2 0
  bw_A := by
    intro d hd
    apply span_by_linear (M:=mat (matrix P).transpose)
    intro j
    have e := funext (cert.bA d hd j)
    rw [N0,action_eq] at e
    rw [e]
    exact combo_mem P.genB d 3 j.val
  bw_Y := by
    intro d hd
    apply span_by_linear (M:=diag (DualSupport12.reflected (matrix P)))
    intro j
    have e := funext (cert.bY d hd j)
    rw [reflected_eq cert] at e
    change DualSupport12.reflected (matrix P) * P.genB j.val ∈ _
    rw [e]
    exact combo_mem P.genB d 4 j.val
  bw_primitive := by
    intro d hd
    rw [← B_eq cert, funext (cert.bP d hd)]
    exact combo_mem P.genB d 5 0
  bw_scalar_zero := by
    intro d hd j hj w hw
    rw [row_apply, dotProduct_comm, ← row_apply, ← node_eq cert]
    exact span_by_zero P.genB d (M:=row (P.c^j)) (fun i => by
      rw [row_apply, dotProduct_comm, ← row_apply, ← pair_eq]
      exact cert.bSilent d hd j hj i) w hw
  bridge_A := by
    apply span_by_linear (M:=mat (matrix P))
    intro i
    have hi : i.val < 3 := i.isLt.trans_le (Nat.min_le_left ..)
    rw [← action_eq]
    exact checked_high cert _ (cert.fASilent ⟨i.val,hi⟩) (cert.fAMoment ⟨i.val,hi⟩)
  bridge_primitive := by
    rw [← F_eq cert]
    exact checked_high cert _ cert.fPSilent cert.fPMoment
  scalar := by
    intro j hj
    simpa only [pair_eq, node_eq cert] using cert.scalar j hj
  units := units

theorem order_twelve (cert : Receipts P)
    (units : ∀ j < 5, IsUnit (((j+1 : Nat) : R))) :
    HasOrder 12 (matrix P) P.b :=
  DualSupport12.LowChecks.hasOrder (lowChecks cert units)

def nextTree : FiniteRootedTree := bushyTree 13

theorem next_size : (nextTree.order:Nat) ≤ 13 := by decide +kernel

theorem next_defect_eq (cert : Receipts P) :
    nextDefect P = ((nextTree.factorial : Nat) : R) * (P.b ⬝ᵥ Φ nextTree (matrix P)) - 1 := by
  have hf : (nextTree.factorial:Nat) = 13 := by decide +kernel
  rw [nextDefect, pair_eq, node_eq cert, hf, nextTree, Φ_bushyTree]
  rfl

theorem nextUnit (cert : Receipts P) :
    IsUnit (((nextTree.factorial : Nat) : R) * (P.b ⬝ᵥ Φ nextTree (matrix P)) - 1) :=
  next_defect_eq cert ▸ IsUnit.of_mul_eq_one P.starInverse cert.nextUnit

end RKResearch.Certified.DualSupport12VectorReplay
