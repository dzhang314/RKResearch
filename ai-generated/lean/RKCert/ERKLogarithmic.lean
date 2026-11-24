module
public import RKCert.ERKDoublingBand
public import RKCert.ERKGradeFive
public import Mathlib.Data.Nat.Log

@[expose] public section
namespace RKCert.Endpoint
open RKCert.Paired Module
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- The genuine strict growth on each separated grade, summed over a subinterval. -/
private theorem rank_interval {A : Fin s → Fin s → K} (ha : StrictLower A) {q : ℕ}
    (hs : Separated A q) (n d : ℕ) (hn : 1≤n) (h : n+d≤q) :
    finrank K (zeroSpace A n)+d ≤ finrank K (zeroSpace A (n+d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hl := ih (by omega)
    have hg := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha hs
      (j:=n+d) (by omega) h)
    rw [show n+(d+1)=n+d+1 by omega]
    omega

/-- Strict growth plus the proved band obstruction gives at least one
surplus rank between j and 2j. -/
theorem doubling_rank_surplus {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j : ℕ)
    (hj : 5≤j) (hp : 4*j≤p) :
    finrank K (zeroSpace A j)+j+1≤finrank K (zeroSpace A (2*j)) := by
  have sPos := explicit_order_le_stages ha ho
  have hs : Separated A (2*j) := explicit_separated ha ho (by omega) (by omega)
  by_contra! low
  apply no_flat_doubling_band ha ho j hj hp
  intro a h
  have front := rank_interval ha hs j a (by omega) (by omega)
  have back := rank_interval ha hs (j+a+1) (j-(a+1)) (by omega) (by omega)
  rw [show j+a+1+(j-(a+1))=2*j by omega] at back
  omega

/-- A general parameterized bound: every available doubling of the actual
grade-five seed costs one further stage. -/
theorem logarithmic_erk_field_dyadic {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (h : ℕ)
    (budget : 10*2^h≤p) : (3*p+1)/2-1+h≤s := by
  let q := p/2
  have ph (k : ℕ) : 0<2^k := pow_pos (by decide) _
  have hs := explicit_order_le_stages ha ho
  have Qsep : Separated A q := explicit_separated ha ho (by dsimp [q]; omega) (by have := ph h; omega)
  have q5 : 5≤q := by have := ph h; dsimp [q]; omega
  have base := grade_five_surplus ha (Qsep.mono q5)
  have band (k : ℕ) (hk : 5*2^k≤q) : 5*2^k+k≤finrank K (zeroSpace A (5*2^k)) := by
    induction k with
    | zero => simpa using base
    | succ k ih =>
      have he : 5*2^(k+1)=2*(5*2^k) := by rw [pow_succ]; ring
      rw [he] at hk ⊢
      have pn := ph k
      have head := ih (by omega)
      have hg := doubling_rank_surplus ha ho (5*2^k) (by omega) (by dsimp [q] at hk; omega)
      omega
  have bq : 5*2^h≤q := by dsimp [q]; omega
  have grow := rank_interval ha Qsep (5*2^h) (q-5*2^h) (by have := ph h; omega) (by omega)
  rw [show 5*2^h+(q-5*2^h)=q by omega] at grow
  have initial := band h bq
  have fq : q+h≤finrank K (zeroSpace A q) := by omega
  have fr := explicit_treeSpace_rank ha ho (q:=q) (by dsimp [q]; omega) (by omega)
  by_cases hpar : p%2=0
  · have hh := backward_count ha ho q (q-2) (by dsimp [q]; omega)
    dsimp [q] at *
    omega
  · have hh := backward_endpoint_count ha ho q (q-1) (by dsimp [q]; omega) (by dsimp [q]; omega)
    dsimp [q] at *
    omega

end RKCert.Endpoint

namespace RKCert
/-- The unconditional, characteristic-zero ERK logarithmic lower bound.
Even arbitrary commutative characteristic-zero rings (possibly with zero
divisors) are covered by the common exact field-specialization theorem. -/
theorem logarithmic_erk_charZero {R : Type*} [CommRing R] [CharZero R] {s p : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p) :
    (3*p+1)/2-1+Nat.log 2 (p/10)≤s := by
  have e := Nat.pow_log_le_self 2 (by omega : p/10≠0)
  apply explicit_of_charZero_fields (fun K _ _ _ _ hA hO =>
    Endpoint.logarithmic_erk_field_dyadic hA hO (Nat.log 2 (p/10)) (by omega)) ha ho

/-- Checked order-20 characteristic-zero specialization from actual rooted trees. -/
theorem explicit_order20_ge30_charZero {R : Type*} [CommRing R] [CharZero R] {s : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 20) : 30≤s := by
  have h := logarithmic_erk_charZero ha ho (by decide)
  exact (show (3*20+1)/2-1+Nat.log 2 (20/10)=30 by decide) ▸ h
end RKCert
