module

public import RKCert.ReviewedNative.PolynomialStageSeparation
public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-! # Paid terminal moment anchors on the actual native tableau

The scalar budget uses only the true defect space and ordinary native probes.
The transport uses the strict physical last column, not a condensed tableau.
No shape, tag placement, Jacobi arithmetic or stencil is assumed.
-/

namespace RKResearch.Certified.Graded.PaidTerminalAnchor

open RKResearch Polynomial
open RKResearch.Certified.Graded.Reverse (coordinate row_coordinate zeroAt mem_zeroAt)
open scoped Matrix

variable {ι K : Type*} [Fintype ι] [Field K]

/-- The literal original coordinate is represented by a pure clock polynomial
and a paid defect, with no restriction on the defect's individual support. -/
structure Profile (A : Matrix ι ι K) (a : ℕ) (t : ι) (α : K)
    (Q : K[X]) (f : ι → K) : Prop where
  degree : Q.natDegree ≤ a
  correction_mem : f ∈ zeroSpace A a
  equation : evalNodes A Q + f = α • coordinate (K:=K) t

variable {A : Matrix ι ι K} {b : ι → K} {p a : ℕ} {t : ι}
variable {α : K} {Q : K[X]} {f : ι → K}

/-- Every paid ordinary moment of the pure part is the one-coordinate
moment. Neither a clock-one assumption nor characteristic zero is needed. -/
theorem Profile.moment (H : Profile A a t α Q f) (ho : HasOrder p A b)
    {k : ℕ} (pay : k+a+1 ≤ p) :
    (primitive (X^k * Q)).eval 1 = α * (b t * (nodes A t)^k) := by
  have fzero : probe A b k f = 0 := probe_zeroSpace ho pay H.correction_mem
  have coordProbe :
      probe A b k (coordinate (K:=K) t) = b t * (nodes A t)^k :=
    row_coordinate (fun i => b i * (nodes A i)^k) t
  have hpure : probe A b k (evalNodes A Q) = α * (b t * (nodes A t)^k) := by
    simpa only [map_add, map_smul, fzero, add_zero, smul_eq_mul, coordProbe]
      using congrArg (probe A b k) H.equation
  have payQ : k+Q.natDegree+1 ≤ p :=
    (Nat.add_le_add_right (Nat.add_le_add_left H.degree k) 1).trans pay
  exact (probe_evalNodes ho Q k payQ).symm.trans hpure

/-- At the actual clock one, all paid terminal moments have the same value. -/
theorem Profile.moment_at_one (H : Profile A a t α Q f) (ho : HasOrder p A b)
    (clock : nodes A t = 1) {k : ℕ} (pay : k+a+1 ≤ p) :
    (primitive (X^k * Q)).eval 1 = α * b t := by
  simpa only [clock, one_pow, mul_one] using H.moment ho (k:=k) pay

/-- The primitive's endpoint value equals scale times physical live mass.
No choice of clock roots or off-mass cancellation enters the calculation. -/
theorem Profile.anchor_value (H : Profile A a t α Q f) (ho : HasOrder p A b)
    (pay : a+1 ≤ p) : (primitive Q).eval 1 = α * b t := by
  have paid : 0+a+1 ≤ p := by simpa only [Nat.zero_add] using pay
  simpa only [pow_zero, one_mul, mul_one] using H.moment ho (k:=0) paid

theorem Profile.anchor_nonzero (H : Profile A a t α Q f) (ho : HasOrder p A b)
    (pay : a+1 ≤ p) (scale : α ≠ 0) (live : b t ≠ 0) :
    (primitive Q).eval 1 ≠ 0 := by
  rw [H.anchor_value ho pay]
  exact mul_ne_zero scale live

/-- If the physical coordinate lies in the actual tree space, no polynomial
representation needs to be supplied by the consumer. -/
theorem exists_profile_of_treeSpace (ho : HasOrder p A b) (pay : a+1 ≤ p)
    (ht : coordinate (K:=K) t ∈ treeSpace A a) :
    ∃ Q : K[X], ∃ f : ι → K, Profile A a t 1 Q f := by
  classical
  rw [treeSpace_coeff_sup ho pay] at ht
  obtain ⟨u, hu, f, hf, eq⟩ := Submodule.mem_sup.mp ht
  obtain ⟨q, rfl⟩ := hu
  let Q : K[X] := ofFn (a+1) q
  have hd : Q.natDegree ≤ a :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos a) q)
  have hQ : evalNodes A Q = coeffEval A a q := by
    rw [evalNodes_eq_coeffEval A Q hd]
    apply congrArg (coeffEval A a)
    funext i
    exact ofFn_coeff_eq_val_of_lt q i.isLt
  exact ⟨Q, f, ⟨hd, hf, by simpa only [hQ, one_smul] using eq⟩⟩

/-- Strictness at a maximal physical index makes its original column zero. -/
theorem mat_coordinate_eq_zero_of_maximal [LE ι]
    (ha : ∀ i j, i ≤ j → A i j = 0) (maximal : ∀ i, i ≤ t) :
    mat A (coordinate (K:=K) t) = 0 := by
  classical
  funext i
  rw [mat_apply, coordinate, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply]
  exact ha i t (maximal i)

/-- Propagate the paid terminal profile to the genuine next defect grade.
The only physical-row hypothesis needed for this lemma is A e_t=0. -/
theorem Profile.primitive_mem [CharZero K] (H : Profile A a t α Q f)
    (kill : mat A (coordinate (K:=K) t) = 0) :
    evalNodes A (primitive Q) ∈ zeroSpace A (a+1) := by
  have shifted : mat A f ∈ zeroSpace A (a+1) :=
    mat_zeroSpace_charZero A a H.correction_mem
  have defect : mat A (evalNodes A Q) - evalNodes A (primitive Q) ∈
      zeroSpace A (a+1) := primitive_defect A Q H.degree
  have killed : mat A (evalNodes A Q) + mat A f = 0 := by
    simpa only [map_add, map_smul, kill, smul_zero] using congrArg (mat A) H.equation
  have eq :
      (mat A (evalNodes A Q) - evalNodes A (primitive Q)) + mat A f =
        -evalNodes A (primitive Q) := by
    rw [sub_eq_add_neg, add_right_comm, killed, zero_add]
  have paid := (zeroSpace A (a+1)).add_mem defect shifted
  rw [eq] at paid
  simpa only [neg_neg] using (zeroSpace A (a+1)).neg_mem paid

/-- Subtract the canonical scalar multiple of the paid primitive that kills the
actual terminal coordinate, keeping the original defect grade. -/
theorem Profile.normalize [CharZero K] (H : Profile A a t α Q f) (ho : HasOrder p A b)
    (pay : a+1 ≤ p) (clock : nodes A t = 1) (scale : α ≠ 0) (live : b t ≠ 0)
    (kill : mat A (coordinate (K:=K) t) = 0)
    {w : ι → K} (hw : w ∈ zeroSpace A (a+1)) :
    w - (w t / (α * b t)) • evalNodes A (primitive Q) ∈
      zeroAt (zeroSpace A (a+1)) t := by
  have value : evalNodes A (primitive Q) t = α * b t := by
    rw [evalNodes_apply, clock]
    exact H.anchor_value ho pay
  refine mem_zeroAt.mpr ⟨(zeroSpace A (a+1)).sub_mem hw
    ((zeroSpace A (a+1)).smul_mem _ (H.primitive_mem kill)), ?_⟩
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, value]
  rw [div_mul_cancel₀ _ (mul_ne_zero scale live), sub_self]

section Physical

variable {s : ℕ}
variable {T : Matrix (Fin (s+1)) (Fin (s+1)) K} {w : Fin (s+1) → K}

/-- The origin evaluates to zero in the pure part of any such profile whose
terminal clock is one. This uses the actual strict first row. -/
theorem Profile.origin_eq_zero {u : Fin (s+1)} {F : Fin (s+1) → K}
    (H : Profile T a u α Q F) (ha : ∀ i j, i ≤ j → T i j = 0)
    (clock : nodes T u = 1) : Q.eval 0 = 0 := by
  have row0 (j : Fin (s+1)) : T 0 j = 0 := ha 0 j (Fin.zero_le j)
  have c0 : nodes T (0 : Fin (s+1)) = 0 := by
    simp [nodes, Matrix.mulVec, dotProduct, row0]
  have u0 : (0 : Fin (s+1)) ≠ u := by
    intro he
    rw [←he, c0] at clock
    exact zero_ne_one clock
  have e0 : coordinate (K:=K) u (0 : Fin (s+1)) = 0 := by
    classical
    simp [coordinate, u0]
  have f0 : F 0 = 0 := origin_zeroSpace ha a H.correction_mem
  simpa only [Pi.add_apply, Pi.smul_apply, evalNodes_apply, c0, f0, add_zero,
    smul_eq_mul, e0, mul_zero] using congrFun H.equation (0 : Fin (s+1))

/-- Actual strict last-column consumer of a reviewed terminal tree-space
membership. It produces both the polynomial profile and the paid nonzero
anchor on the original physical rows. -/
theorem strict_last_anchor_of_treeSpace [CharZero K]
    (ha : ∀ i j, i ≤ j → T i j = 0)
    (ho : HasOrder p T w) (pay : a+1 ≤ p)
    (clock : nodes T (Fin.last s) = 1) (live : w (Fin.last s) ≠ 0)
    (col : coordinate (K:=K) (Fin.last s) ∈ treeSpace T a) :
    ∃ Q : K[X], ∃ f : Fin (s+1) → K,
      Profile T a (Fin.last s) 1 Q f ∧ Q.eval 0 = 0 ∧
      (primitive Q).eval 1 = w (Fin.last s) ∧ (primitive Q).eval 1 ≠ 0 ∧
      evalNodes T (primitive Q) ∈ zeroSpace T (a+1) := by
  obtain ⟨Q, f, H⟩ := exists_profile_of_treeSpace ho pay col
  have kill : mat T (coordinate (K:=K) (Fin.last s)) = 0 :=
    mat_coordinate_eq_zero_of_maximal ha (fun i => Fin.le_last i)
  have value : (primitive Q).eval 1 = w (Fin.last s) := by
    simpa only [one_mul] using H.anchor_value ho pay
  exact ⟨Q, f, H, H.origin_eq_zero ha clock, value,
    H.anchor_nonzero ho pay one_ne_zero live, H.primitive_mem kill⟩

end Physical

end RKResearch.Certified.Graded.PaidTerminalAnchor
