module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicDigits
public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrigin
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section

/-! Unbounded scalar Hensel over the algebraic inverse-limit model of
29-adic integers. No topological or analytic library is required. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Digits
open Polynomial

private structure RootAt (P : (n : ℕ) → Polynomial (Level n)) (a : F) (n : ℕ) where
  val : Level n
  root : (P n).eval val = 0
  residue : res n val = a

theorem lift_compatible (P : (n : ℕ) → Polynomial (Level n))
    (hP : ∀ n, (P (n+1)).map (down n) = P n)
    (a : F) (hbase : (P 0).eval a = 0)
    (hder : (P 0).derivative.eval a ≠ 0) :
    ∃ f : (n : ℕ) → Level n,
      (∀ n, (P n).eval (f n) = 0) ∧
      (∀ n, down n (f (n+1)) = f n) ∧ f 0 = a := by
  have hreduce : ∀ n, (P n).map (res n) = P 0 := by
    intro n
    induction n with
    | zero =>
      rw [res_zero]
      change (P 0).map (RingHom.id (Level 0)) = P 0
      exact Polynomial.map_id
    | succ n ih => rw [← res_comp_down n, ← Polynomial.map_map, hP n, ih]
  have hnext : ∀ n (r : RootAt P a n), ∃ s : RootAt P a (n+1), down n s.val = r.val := by
    intro n r
    have hr : ((P (n+1)).map (down n)).eval r.val = 0 := by rw [hP n]; exact r.root
    have hd : ((P (n+1)).map (res (n+1))).derivative.eval (res n r.val) ≠ 0 := by
      rw [hreduce (n+1),r.residue]
      exact hder
    obtain ⟨s,hs,hdown⟩ := step n (P (n+1)) r.val hr hd
    refine ⟨⟨s,hs,?_⟩,hdown⟩
    rw [← res_down n, hdown]
    exact r.residue
  let first : RootAt P a 0 := ⟨a,hbase,DFunLike.congr_fun res_zero a⟩
  let seq : (n : ℕ) → RootAt P a n :=
    Nat.rec first (fun n r => Classical.choose (hnext n r))
  refine ⟨(fun n => (seq n).val), (fun n => (seq n).root), ?_, rfl⟩
  intro n
  exact Classical.choose_spec (hnext n (seq n))

open scoped Ring
noncomputable section

/-- The compatible inverse limit of the finite rings modulo the positive
powers of 29, with all operations coordinatewise. -/
def compatible : Subring ((n : ℕ) → Level n) where
  carrier := { f | ∀ n, down n (f (n+1)) = f n }
  zero_mem' := by intro n; exact map_zero _
  one_mem' := by intro n; exact map_one _
  add_mem' := by
    intro x y hx hy n
    change down n (x (n+1)+y (n+1)) = x n+y n
    rw [map_add,hx n,hy n]
  mul_mem' := by
    intro x y hx hy n
    change down n (x (n+1)*y (n+1)) = x n*y n
    rw [map_mul,hx n,hy n]
  neg_mem' := by
    intro x hx n
    change down n (-x (n+1)) = -x n
    rw [map_neg,hx n]

abbrev Z29Limit := compatible

def project (n : ℕ) : Z29Limit →+* Level n :=
  (Pi.evalRingHom Level n).comp compatible.subtype

def reduce : Z29Limit →+* F := project 0

theorem project_down (n : ℕ) (x : Z29Limit) :
    down n (project (n+1) x) = project n x := x.property n

theorem res_project (x : Z29Limit) (n : ℕ) : res n (project n x) = reduce x := by
  induction n with
  | zero => exact DFunLike.congr_fun res_zero (project 0 x)
  | succ n ih => rw [← res_down n, project_down,ih]

instance localReduce : IsLocalHom reduce where
  map_nonunit x hx := by
    have hu (n : ℕ) : IsUnit (project n x) := by
      apply IsUnit.of_map (res n)
      rwa [res_project]
    let inv : Z29Limit := ⟨fun n => (project n x)⁻¹ʳ, by
      intro n
      change down n ((project (n+1) x)⁻¹ʳ) = (project n x)⁻¹ʳ
      rw [(hu (n+1)).map_ringInverse (down n), project_down]⟩
    apply IsUnit.of_mul_eq_one inv
    apply Subtype.ext
    funext n
    change project n x * (project n x)⁻¹ʳ = 1
    exact Ring.mul_inverse_cancel _ (hu n)

theorem simpleLift_limit : SimpleLift reduce := by
  intro P a hr hd
  let Q (n : ℕ) := P.map (project n)
  have hQ (n : ℕ) : (Q (n+1)).map (down n) = Q n := by
    change (P.map (project (n+1))).map (down n) = P.map (project n)
    rw [Polynomial.map_map]
    congr 1
    ext x
    exact project_down n x
  obtain ⟨f, hf, hc, h0⟩ := lift_compatible Q hQ a hr hd
  let x : Z29Limit := ⟨f,hc⟩
  refine ⟨x, ?_, h0⟩
  apply Subtype.ext
  funext n
  change project n (P.eval x) = project n 0
  rw [← eval_map_apply, map_zero]
  exact hf n

theorem unique_of_simple_residue (P : Polynomial Z29Limit) (a : F)
    (hr : (P.map reduce).eval a = 0) (hd : (P.map reduce).derivative.eval a ≠ 0) :
    ∃! z : Z29Limit, P.eval z = 0 ∧ reduce z = a := by
  obtain ⟨z,hz,hza⟩ := simpleLift_limit P a hr hd
  refine ⟨z,⟨hz,hza⟩,?_⟩
  intro w hw
  obtain ⟨q,hq⟩ := P.binomExpansion z (w-z)
  rw [show z+(w-z)=w by ring,hw.1,hz,zero_add] at hq
  have hfac : (P.derivative.eval z + q*(w-z))*(w-z) = 0 := by
    calc
      _ = P.derivative.eval z*(w-z) + q*(w-z)^2 := by ring
      _ = 0 := hq.symm
  have H : IsUnit (P.derivative.eval z+q*(w-z)) := by
    apply IsUnit.of_map reduce
    apply isUnit_iff_ne_zero.mpr
    rw [map_add,map_mul,map_sub,hw.2,hza,sub_self,mul_zero,add_zero,
      ← eval_map_apply, ← derivative_map, hza]
    exact hd
  apply sub_eq_zero.mp
  exact H.mul_left_cancel (by rw [hfac,mul_zero])

/-- The literal fixed-q decic and its true origin residual, both ordered
head roots, the paid head guards, and the tail residues coexist in one
compatible 29-adic point. This is a scalar theorem, not a tableau theorem. -/
theorem scalar_existence_limit :
    ∃ c a b : Z29Limit,
      (decic Z29Limit).eval c = 0 ∧ reduce c = 2 ∧ origin c = 0 ∧
      (headQuadratic c).eval a = 0 ∧ reduce a = 11 ∧
      (headQuadratic c).eval b = 0 ∧ reduce b = 20 ∧ b = headSum c-a ∧
      reduce (hTail c) = 22 ∧ reduce (fTail c) = 7 ∧ reduce (eTail c) = 27 ∧ PaidHead c := by
  obtain ⟨c,a,b,hc,hcr,ha,har,hb,hbr,hab,hh,hf,he,hpaid⟩ :=
    scalar_existence reduce simpleLift_limit
  exact ⟨c,a,b,hc,hcr,origin_zero_of_decic reduce hcr hc,ha,har,hb,hbr,hab,hh,hf,he,hpaid⟩

end
end RKResearch.Certified.ERK10FixedQ29Adic.Digits

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Digits.lift_compatible
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Digits.simpleLift_limit
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Digits.unique_of_simple_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Digits.scalar_existence_limit
