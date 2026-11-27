module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKResearch.ERK
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! An integer-pair certificate for a rational-quadratic explicit tableau.
Numerators live in Z[S]/(S²-δ) and every coefficient has one common
integer denominator. No field, division, characteristic or order on
the target ring is required. -/

namespace RKResearch.Certified.ERKQuadraticIntegerReplay
open FiniteRootedTree
open scoped Matrix

abbrev Pair := Int × Int

def pack (j : Int) : Pair := (j,0)
def add (p q : Pair) : Pair := (p.1 + q.1, p.2 + q.2)
def mul (δ : Int) (p q : Pair) : Pair :=
  (p.1*q.1 + δ*p.2*q.2, p.1*q.2 + p.2*q.1)

def val {R : Type*} [CommRing R] (s : R) (p : Pair) : R :=
  (p.1 : R) + s * (p.2 : R)

variable {R : Type*} [CommRing R]
theorem val_pack (s : R) (j : Int) : val s (pack j) = j := by simp [val,pack]
theorem val_add (s : R) (p q : Pair) : val s (add p q) = val s p + val s q := by
  simp [val,add]; ring
theorem val_mul {δ : Int} {s : R} (hs : s*s = (δ:R)) (p q : Pair) :
    val s (mul δ p q) = val s p * val s q := by
  simp only [val,mul,Int.cast_add,Int.cast_mul]
  calc
    _ = (p.1:R)*q.1 + s*((p.1:R)*q.2 + (p.2:R)*q.1) +
      (δ:R)*p.2*q.2 := by ring
    _ = _ := by rw [←hs]; ring

def dot (δ : Int) : (n : Nat) → (Fin n → Pair) → (Fin n → Pair) → Pair
  | 0, _, _ => pack 0
  | n+1, a, b => add (mul δ (a 0) (b 0)) (dot δ n (a ∘ Fin.succ) (b ∘ Fin.succ))

theorem val_dot {δ : Int} {s : R} (hs : s*s = (δ:R)) (n : Nat) (a b : Fin n → Pair) :
    val s (dot δ n a b) = (fun i => val s (a i)) ⬝ᵥ (fun i => val s (b i)) := by
  induction n with
  | zero => simp [dot,val_pack,dotProduct]
  | succ n ih =>
    simp only [dot,val_add,val_mul hs,ih,dotProduct,Fin.sum_univ_succ,Function.comp_apply]

/-- Integer numerator of the ordinary (non-integrated) stage weights. -/
def profile (δ : Int) {n : Nat} (M : Fin n → Fin n → Pair) :
    FiniteRootedTree → Fin n → Pair
  | .leaf => fun _ => pack 1
  | .butcherProduct u v => fun i =>
    mul δ (profile δ M u i) (dot δ n (M i) (profile δ M v))

/-- Unnormalized stage scale: `d^(order-1)`, without a subtraction. -/
def scale {T : Type*} [Monoid T] (d : T) : FiniteRootedTree → T
  | .leaf => 1
  | .butcherProduct u v => scale d u * (d * scale d v)

theorem scales_cancel (D : Int) (d : R) (h : (D:R)*d=1) (t : FiniteRootedTree) :
    ((scale D t : Int) : R) * scale d t = 1 := by
  induction t with
  | leaf => simp [scale]
  | butcherProduct u v iu iv =>
    simp only [scale,Int.cast_mul]
    calc
      _ = ((scale D u : Int):R)*scale d u *
        (((D:R)*d) * (((scale D v : Int):R)*scale d v)) := by ring
      _ = _ := by rw [iu, iv, h]; simp

def tableau {n : Nat} (s d : R) (M : Fin n → Fin n → Pair) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun i j => val s (M i j)*d

def weights {n : Nat} (s d : R) (w : Fin n → Pair) : Fin n → R :=
  fun i => val s (w i)*d

theorem dot_scale {n : Nat} (x y : R) (a b : Fin n → R) :
    (fun i => a i*x) ⬝ᵥ (fun i => b i*y) = (a ⬝ᵥ b)*(x*y) := by
  unfold dotProduct
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem phi_scaled {δ : Int} {n : Nat} {s : R} (hs : s*s=(δ:R)) (d : R)
    (M : Fin n → Fin n → Pair) (t : FiniteRootedTree) (i : Fin n) :
    Φ t (tableau s d M) i = val s (profile δ M t i) * scale d t := by
  induction t generalizing i with
  | leaf => simp [profile,scale,val_pack]
  | butcherProduct u v iu iv =>
    change Φ u (tableau s d M) i * ((fun j => val s (M i j)*d) ⬝ᵥ Φ v (tableau s d M)) = _
    have hv : Φ v (tableau s d M) = fun j => val s (profile δ M v j)*scale d v := funext iv
    rw [iu, hv, dot_scale]
    simp only [profile, val_mul hs, val_dot hs, scale]
    ring

def numer (δ : Int) {n : Nat} (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (t : FiniteRootedTree) : Pair :=
  mul δ (pack (t.factorial : Nat)) (dot δ n w (profile δ M t))

theorem paid_eq {δ : Int} {n : Nat} {s : R} (hs : s*s=(δ:R)) (d : R)
    (M : Fin n → Fin n → Pair) (w : Fin n → Pair) (t : FiniteRootedTree) :
    (t.factorial : R) * (weights s d w ⬝ᵥ Φ t (tableau s d M)) =
      val s (numer δ M w t) * (d * scale d t) := by
  have ht : Φ t (tableau s d M) = fun j => val s (profile δ M t j)*scale d t :=
    funext (phi_scaled hs d M t)
  rw [ht]
  unfold weights
  rw [dot_scale]
  simp only [numer,val_mul hs,val_pack,val_dot hs,Int.cast_natCast]
  ring

def checkOn (δ : Int) {n : Nat} (D : Int) (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (k : Nat) : Bool :=
  (treesOfOrderSucc k).all fun t => decide (numer δ M w t = pack (D * scale D t))

theorem order_of_check {δ : Int} {n p : Nat} (D : Int) {s : R} (hs : s*s=(δ:R)) (d : R)
    (hd : (D:R)*d = 1) (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (h : ∀ k < p, checkOn δ D M w k = true) : HasOrder p (tableau s d M) (weights s d w) := by
  intro t ht
  have ht0 := t.order.pos
  have hsiz : (t.order : Nat) = ((t.order:Nat)-1)+1 := by omega
  have hmem := (mem_treesOfOrderSucc _ _).mpr hsiz
  obtain hcheck := h ((t.order:Nat)-1) (by omega)
  have hn := of_decide_eq_true (List.all_eq_true.mp hcheck t hmem)
  rw [paid_eq hs d, hn, val_pack, Int.cast_mul]
  calc
    _ = ((D:R)*d) * (((scale D t:Int):R)*scale d t) := by ring
    _ = _ := by rw [hd, scales_cancel D d hd t]; simp

/-- A denominator-cleared single-tree failure, with a unit defect after
specialization. Both computations are entirely integral. -/
theorem exact_defect {δ : Int} {n : Nat} (D K : Int) {s : R} (hs : s*s=(δ:R))
    (d : R) (hd : (D:R)*d=1) (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (t : FiniteRootedTree) (h : mul δ (pack K) (numer δ M w t) =
      pack ((K+1) * (D * scale D t))) :
    (K:R) * ((t.factorial : R) * (weights s d w ⬝ᵥ Φ t (tableau s d M)) - 1) = 1 := by
  have heq := congrArg (val s) h
  simp only [val_mul hs, val_pack, Int.cast_mul, Int.cast_add, Int.cast_one] at heq
  rw [paid_eq hs d]
  have hscale : ((D:R)*(scale D t : Int))*(d * scale d t) = 1 := by
    calc
      _ = ((D:R)*d) * (((scale D t : Int):R)*scale d t) := by ring
      _ = 1 := by rw [hd,scales_cancel D d hd t]; simp
  calc
    _ = ((K:R)*val s (numer δ M w t))*(d * scale d t) - (K:R) := by ring
    _ = ((K:R)+1)*(((D:R)*(scale D t : Int))*(d * scale d t)) - (K:R) := by rw [heq]; ring
    _ = 1 := by rw [hscale]; ring

end RKResearch.Certified.ERKQuadraticIntegerReplay
