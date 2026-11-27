module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Exact finite arithmetic for the strict SDIRK(8,7) midpoint

This kernel-verifiable scalar layer takes the two chronological end charts,
four causal cancellations, and the genuine clock/first-seed moments as
hypotheses. It does not by itself import or assume a tree-to-profile bridge.
-/

namespace RKResearch.Certified.SDIRKSeven.F19
set_option maxHeartbeats 1000000
open scoped BigOperators Matrix

instance prime19 : Fact (Nat.Prime 19) := ⟨by decide⟩
abbrev K := ZMod 19

structure Key where
  z : Fin 19
  u : Fin 19
  v : Fin 19
  apFront : Bool
  apRear : Bool
deriving DecidableEq

def Z (k : Key) : K := k.z.val
def U (k : Key) : K := k.u.val
def V (k : Key) : K := k.v.val

def kap (u : K) := 1+2*u-u^2
def den (u : K) := -2+u+4*u^2-u^3
def rn (u : K) := 2*u*(3*u-2)
def w (u : K) (ap : Bool) := if ap then 2*u else 2-u

def guard (u : K) (ap : Bool) : Prop :=
  u≠0 ∧ if ap then den u≠0 ∧ rn u≠0 else u≠1 ∧ u≠2

instance (u : K) (ap : Bool) : Decidable (guard u ap) := by unfold guard; split <;> infer_instance

def chart (k : Key) : Prop :=
  Z k≠0 ∧ guard (U k) k.apFront ∧ guard (V k) k.apRear

instance (k : Key) : Decidable (chart k) := by unfold chart; infer_instance

def thirdSeed (u : K) (ap : Bool) :=
  if ap then kap (w u ap)+2*(rn u/den u)*u else kap u

def h (u : K) (ap : Bool) : Fin 3→K :=
  if ap then ![u^2*(u-1),-u*(u-2)*(2*u-1),(u-2)*(u-1)^2/2]
  else ![1,-2,1/2]

def n (f : Fin 3→K) : Fin 4→K :=
  ![-f 0, f 0-f 1, f 1/2-f 2, f 2/3]

def cross {a b : ℕ} (z : K) (f : Fin a→K) (g : Fin b→K) (d : ℕ) : K :=
  ∑ i, ∑ j,
    f i * g j * z^(i.val+j.val+d) * (Nat.factorial (i.val+d) : K) *
      (Nat.factorial j.val : K) / (Nat.factorial (i.val+j.val+d+1) : K)

def front (k : Key) := h (U k) k.apFront
def rear (k : Key) := h (V k) k.apRear
def q (k : Key) := cross (Z k) (n (front k)) (n (rear k)) 0
def t (k : Key) := cross (Z k) (front k) (n (rear k)) 0
def l (k : Key) := cross (Z k) (front k) (n (rear k)) 1
def r (k : Key) := cross (Z k) (n (front k)) (rear k) 1
def overlap (k : Key) (a b : K) :=
  cross (Z k) (front k) (rear k) 2
    - (a+b)*cross (Z k) (front k) (rear k) 1
    + a*b*cross (Z k) (front k) (rear k) 0

def nodes (k : Key) (a b : K) : Fin 8→K :=
  ![1,1+U k,1+w (U k) k.apFront,a,b,
    Z k-1-w (V k) k.apRear,Z k-1-V k,Z k-1]

def inferredNodes (k : Key) := nodes k (l k/t k) (r k/t k)

def evalPoly (f : Fin 7→K) (x : K) := ∑ j, f j*x^j.val
def mean (z : K) (f : Fin 7→K) := ∑ j, f j*z^j.val/((j.val+1:ℕ):K)

def quadrature (z : K) (x b : Fin 8→K) : Prop :=
  ∀ j : Fin 7, (∑ i, b i*x i^j.val)=z^j.val/((j.val+1:ℕ):K)

theorem paid_poly {z : K} {x b : Fin 8→K} (ho : quadrature z x b)
    (p : Fin 7→K) : (∑ i, b i*evalPoly p (x i))=mean z p := by
  simp only [evalPoly,mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_assoc,←ho j,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def seed (k : Key) (a b d : K) : Fin 8→K :=
  ![1,kap (U k),thirdSeed (U k) k.apFront,a,b,
    d*thirdSeed (V k) k.apRear,d*kap (V k),d]

def firstSeedLaw (k : Key) (x w : Fin 8→K) (a b d : K) : Prop :=
  ∀ j : Fin 5, (∑ i, w i*x i^j.val*seed k a b d i)=0

def mask (w : Fin 8→K) : Prop := (∀ i,w i≠0) ∨ (w 0=0 ∧ w 1=0 ∧ w 2=0)
instance (w : Fin 8→K) : Decidable (mask w) := by unfold mask; infer_instance

/-- The four columns of the augmented linear first-seed system, placing
the known head at index 3. The three unknowns are stage 4, stage 5,
and the terminal seed, in that order. -/
def seedMatrix (k : Key) (x w : Fin 8→K) (j : Fin 5) : Fin 4→K :=
  let m (i : Fin 8) := w i*x i^j.val
  ![m 3,m 4,m 5*thirdSeed (V k) k.apRear+m 6*kap (V k)+m 7,
    m 0+m 1*kap (U k)+m 2*thirdSeed (U k) k.apFront]

private theorem fold_firstSeedLaw (k : Key) (x w : Fin 8→K) (a b d : K)
    (law : firstSeedLaw k x w a b d) (j : Fin 5) :
    seedMatrix k x w j 0*a+seedMatrix k x w j 1*b+
      seedMatrix k x w j 2*d+seedMatrix k x w j 3=0 := by
  have h := law j
  simp [seedMatrix,seed,Fin.sum_univ_succ] at h ⊢
  linear_combination h

inductive Recipe where
  | rejectQuad (p : Fin 7→K)
  | certifyFamily (free : Fin 8) (rows : Fin 8→Fin 7→K) (dual : Fin 19→Fin 5→K)

def family (k : Key) (free : Fin 8) (rows : Fin 8→Fin 7→K) (a : K) : Fin 8→K :=
  let x := inferredNodes k
  fun i=> if i=free then a else mean (Z k) (rows i)-a*evalPoly (rows i) (x free)

def quadReject (k : Key) (p : Fin 7→K) : Prop :=
  (∀ i,evalPoly p (inferredNodes k i)=0) ∧ mean (Z k) p≠0
instance (k : Key) (p : Fin 7→K) : Decidable (quadReject k p) := by unfold quadReject; infer_instance

def familyRows (k : Key) (free : Fin 8) (p : Fin 8→Fin 7→K) : Prop :=
  ∀ i, i≠free → ∀ j, j≠free →
      evalPoly (p i) (inferredNodes k j) = if j=i then 1 else 0
instance (k : Key) (free : Fin 8) (p : Fin 8→Fin 7→K) : Decidable (familyRows k free p) := by
  unfold familyRows; infer_instance

def witness (k : Key) (b : Fin 8→K) (dual : Fin 5→K) : Prop :=
  (∀ j : Fin 3, (∑ i, dual i*seedMatrix k (inferredNodes k) b i (j.castLE (by decide : 3≤4)))=0) ∧
    (∑ i, dual i*seedMatrix k (inferredNodes k) b i 3)=1
instance (k : Key) (b : Fin 8→K) (dual : Fin 5→K) : Decidable (witness k b dual) := by
  unfold witness; infer_instance

def valid (k : Key) : Recipe→Prop
  | .rejectQuad p => quadReject k p
  | .certifyFamily u p ys => familyRows k u p ∧
      ∀ j : Fin 19, let b := family k u p (j.val:K); mask b → witness k b (ys j)

instance (k : Key) (u : Recipe) : Decidable (valid k u) := by cases u <;> unfold valid <;> infer_instance

private theorem family_sound (k : Key) (free : Fin 8) (p : Fin 8→Fin 7→K)
    (hrows : familyRows k free p) (b : Fin 8→K) (hquad : quadrature (Z k) (inferredNodes k) b) :
    b=family k free p (b free) := by
  funext i
  by_cases hi : i=free
  · subst i; simp [family]
  · have exact := paid_poly hquad (p i)
    have single : (∑ j ∈ (Finset.univ.erase free), b j*evalPoly (p i) (inferredNodes k j))=b i := by
      rw [Finset.sum_eq_single i]
      · rw [hrows i hi i hi,ite_eq_left rfl,mul_one]
      · intro j hj hjne
        have f := (Finset.mem_erase.mp hj).1
        rw [hrows i hi j f,ite_eq_right hjne,mul_zero]
      · exact fun h => (h (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)).elim
    have hl : (∑ j, b j*evalPoly (p i) (inferredNodes k j)) =
      b free*evalPoly (p i) (inferredNodes k free)+b i := by
      calc
        _ = b free*evalPoly (p i) (inferredNodes k free) +
             ∑ j ∈ (Finset.univ.erase free), b j*evalPoly (p i) (inferredNodes k j) :=
             (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ free)).symm
        _ = _ := congrArg (fun r : K => b free*evalPoly (p i) (inferredNodes k free)+r) single
    rw [hl] at exact
    unfold family
    rw [ite_eq_right hi]
    linear_combination exact

private theorem contradict_witness (k : Key) (b : Fin 8→K) (dual : Fin 5→K)
    (hw : witness k b dual) (a c d : K)
    (hs : firstSeedLaw k (inferredNodes k) b a c d) : False := by
  let S := seedMatrix k (inferredNodes k) b
  have h0 : (∑ i, dual i*S i 0)=0 := hw.1 0
  have h1 : (∑ i, dual i*S i 1)=0 := hw.1 1
  have h2 : (∑ i, dual i*S i 2)=0 := hw.1 2
  have h3 : (∑ i, dual i*S i 3)=1 := hw.2
  have e : ∑ i, dual i*(S i 0*a+S i 1*c+S i 2*d+S i 3)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [fold_firstSeedLaw k (inferredNodes k) b a c d hs i,mul_zero]
  simp only [mul_add,Finset.sum_add_distrib,←mul_assoc,←Finset.sum_mul,h0,h1,h2,h3,zero_mul,zero_add] at e
  exact one_ne_zero e

theorem prohibit_of_valid (k : Key) (rc : Recipe) (hv : valid k rc) (b : Fin 8→K)
    (hq : quadrature (Z k) (inferredNodes k) b) (hm : mask b) (a c d : K)
    (hs : firstSeedLaw k (inferredNodes k) b a c d) : False := by
  cases rc with
  | rejectQuad p =>
    have e := paid_poly hq p
    have he : (∑ i, b i*evalPoly p (inferredNodes k i))=0 := Finset.sum_eq_zero
      (fun i _=>by rw [hv.1 i,mul_zero])
    exact hv.2 (e.symm.trans he)
  | certifyFamily free p dual =>
    let j : Fin 19 := ⟨(b free).val,(b free).val_lt⟩
    have bj : (j.val:K)=b free := by
      change ((b free).val:K)=b free
      exact ZMod.natCast_zmod_val (b free)
    have e := family_sound k free p hv.1 b hq
    have w := hv.2 j
    rw [bj,←e] at w
    exact contradict_witness k b (dual j) (w hm) a c d hs

end RKResearch.Certified.SDIRKSeven.F19
