module

import RKCert.ReviewedNative.PaidTerminalAnchor

open RKResearch Polynomial
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.PaidTerminalAnchor
open RKResearch.Certified.Graded.Reverse (coordinate zeroAt)

/- The scalar moment and live anchor are native, and field-level. -/
example {ι K : Type*} [Fintype ι] [Field K]
    {A : Matrix ι ι K} {b : ι → K} {p a k : ℕ} {t : ι}
    {α : K} {Q : K[X]} {f : ι → K}
    (H : Profile A a t α Q f) (ho : HasOrder p A b)
    (payk : k+a+1 ≤ p) (pay : a+1 ≤ p)
    (scale : α ≠ 0) (live : b t ≠ 0) :
    (primitive (X^k * Q)).eval 1 = α * (b t * (nodes A t)^k) ∧
      (primitive Q).eval 1 = α * b t ∧ (primitive Q).eval 1 ≠ 0 :=
  ⟨H.moment ho (k:=k) payk, H.anchor_value ho pay, H.anchor_nonzero ho pay scale live⟩

/- The actual vector stays in the next paid defect grade under normalization. -/
example {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    {A : Matrix ι ι K} {b : ι → K} {p a : ℕ} {t : ι}
    {α : K} {Q : K[X]} {f w : ι → K}
    (H : Profile A a t α Q f) (ho : HasOrder p A b)
    (pay : a+1 ≤ p) (clock : nodes A t = 1) (scale : α ≠ 0) (live : b t ≠ 0)
    (kill : mat A (coordinate (K:=K) t) = 0) (hw : w ∈ zeroSpace A (a+1)) :
    evalNodes A (primitive Q) ∈ zeroSpace A (a+1) ∧
      w - (w t / (α * b t)) • evalNodes A (primitive Q) ∈
        zeroAt (zeroSpace A (a+1)) t :=
  ⟨H.primitive_mem kill, H.normalize ho pay clock scale live kill hw⟩

/- The physical strict-last wrapper does not take a prebuilt profile. -/
example {K : Type*} [Field K] [CharZero K] {s p a : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (pay : a+1 ≤ p)
    (clock : nodes A (Fin.last s) = 1) (live : b (Fin.last s) ≠ 0)
    (col : coordinate (K:=K) (Fin.last s) ∈ treeSpace A a) :
    ∃ Q : K[X], ∃ f : Fin (s+1) → K,
      Profile A a (Fin.last s) 1 Q f ∧ Q.eval 0 = 0 ∧
      (primitive Q).eval 1 = b (Fin.last s) ∧ (primitive Q).eval 1 ≠ 0 ∧
      evalNodes A (primitive Q) ∈ zeroSpace A (a+1) :=
  strict_last_anchor_of_treeSpace ha ho pay clock live col

#print axioms RKResearch.Certified.Graded.PaidTerminalAnchor.Profile.moment
#print axioms RKResearch.Certified.Graded.PaidTerminalAnchor.Profile.anchor_nonzero
#print axioms RKResearch.Certified.Graded.PaidTerminalAnchor.Profile.primitive_mem
#print axioms RKResearch.Certified.Graded.PaidTerminalAnchor.Profile.normalize
#print axioms RKResearch.Certified.Graded.PaidTerminalAnchor.strict_last_anchor_of_treeSpace
