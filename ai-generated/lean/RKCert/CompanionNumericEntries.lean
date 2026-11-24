module

public import RKCert.CompanionFiniteMoments

@[expose] public section

/-! # Exact numeric compound entries from interpolation of tiny minors

The polynomial in the companion coordinate has degree at most the
subset size. Small Laplace expansions and a list of linear factors
compute its paid functional without evaluating large polynomial rings. -/
namespace RKCert.Compound
open Polynomial
open scoped Classical
variable {R : Type*} [Field R]

def basisClockList {k : ℕ} (x : Fin (k+1)→R) (i : Fin (k+1)) : List R :=
  List.ofFn fun r : Fin k => x (i.succAbove r)

def basisScale {k : ℕ} (x : Fin (k+1)→R) (i : Fin (k+1)) : R :=
  (List.ofFn fun r : Fin k => (x i-x (i.succAbove r))⁻¹).prod

def numericWeight {k : ℕ} (M j w : ℕ) (u : R) (x : Fin (k+1)→R) (i : Fin (k+1)) : R :=
  (((-1:R)^w)*basisScale x i)*smallFactorMoment M u j (List.replicate w 1++basisClockList x i)

private theorem product_erase (k : ℕ) {S : Type*} [CommMonoid S] (g : Fin (k+1)→S) (i : Fin (k+1)) :
    (∏ j ∈ (Finset.univ.erase i),g j)=(List.ofFn (fun r : Fin k => g (i.succAbove r))).prod := by
  have e : (Finset.univ.erase i : Finset (Fin (k+1)))=Finset.univ.map i.succAboveEmb := by
    ext j
    simp [Finset.mem_erase,Finset.mem_map]
  rw [e,Finset.prod_map,List.prod_ofFn]
  rfl

private theorem basis_factor {k : ℕ} (x : Fin (k+1)→R) (i : Fin (k+1)) :
    Lagrange.basis Finset.univ x i=C (basisScale x i)*linearFactors (basisClockList x i) := by
  unfold Lagrange.basis
  simp_rw [Lagrange.basisDivisor,Finset.prod_mul_distrib,←map_prod,product_erase]
  unfold basisScale linearFactors basisClockList
  rw [List.map_ofFn]
  rfl

private theorem basis_weighted_factor {k : ℕ} (x : Fin (k+1)→R) (i : Fin (k+1)) (w : ℕ) :
    (1-X)^w*Lagrange.basis Finset.univ x i=
      (((-1:R)^w)*basisScale x i) • linearFactors (List.replicate w 1++basisClockList x i) := by
  rw [basis_factor,smul_eq_C_mul]
  unfold linearFactors
  simp only [List.map_append,List.prod_append,List.map_replicate,List.prod_replicate,map_mul,map_pow,
    map_neg,map_one]
  have eq : (1-X:R[X])= -(X-C (1:R)) := by simp
  rw [eq,neg_pow]
  simp only [map_one]
  ring

theorem numericWeight_exact {k : ℕ} (M j w : ℕ) (u : R) (x : Fin (k+1)→R) (i : Fin (k+1)) :
    numericWeight M j w u x i =
      scaledMoment M j (k+w) u ((1-X)^w*Lagrange.basis Finset.univ x i) := by
  unfold numericWeight
  rw [basis_weighted_factor,←scaledMomentLinear_apply,map_smul,smul_eq_mul,
    scaledMomentLinear_apply,smallFactorMoment_exact]
  congr 2
  simp [basisClockList,Nat.add_comm]

/-- The small companion entry after evaluating its outer polynomial
coordinate at an auxiliary interpolation site. -/
def rawEntryValue {n : ℕ} (b : Fin (n+1)→R) (z : R) (i j : Fin n) : R :=
  if j.val+1<n then (if i=j then z else 0)-(if i.val=j.val+1 then 1 else 0)
    else (if i=j then b (Fin.last n)*z else 0)+b i.castSucc

theorem rawEntryValue_exact {n : ℕ} (b : Fin (n+1)→R) (z : R) (i j : Fin n) :
    rawEntryValue b z i j=(rawResolvent b i j).eval z := by
  by_cases step : j.val+1<n <;> by_cases ij : i=j <;> by_cases sh : i.val=j.val+1 <;>
    simp [rawEntryValue,rawResolvent,step,ij,sh]

def numericMomentEntry {n k h : ℕ} (E : OrderedAxes n k h) (M j w : ℕ) (u : R)
    (b : Fin (n+1)→R) (x : Fin (k+1)→R) (i t : Fin h) : R :=
  (List.ofFn fun a : Fin (k+1) =>
    (tinyDet k (Matrix.of fun c d => rawEntryValue b (x a) (E.axis i c) (E.axis t d))) *
      numericWeight M j w u x a).sum

theorem numericMomentEntry_exact {n k h : ℕ} (E : OrderedAxes n k h) (M j w : ℕ) (u : R)
    (b : Fin (n+1)→R) (x : Fin (k+1)→R) (inj : Function.Injective x) (i t : Fin h) :
    numericMomentEntry E M j w u b x i t=rawMomentMatrix M j w u b (E.index i) (E.index t) := by
  let P := rawMinor b (E.index i) (E.index t)
  have deg : P.natDegree≤k := rawMinor_outer_cap _ _ _
  have e : P=Lagrange.interpolate Finset.univ x (fun a=>P.eval (x a)) :=
    Lagrange.eq_interpolate inj.injOn (by
      simp only [Finset.card_univ,Fintype.card_fin]
      exact P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le deg))
  let L : R[X] →ₗ[R] R :=
    (scaledMomentLinear M j (k+w) u).comp (LinearMap.mulLeft R ((1-X)^w))
  have l := congrArg L e
  rw [Lagrange.interpolate_apply,map_sum] at l
  simp_rw [←smul_eq_C_mul,map_smul,smul_eq_mul] at l
  change numericMomentEntry E M j w u b x i t=L P
  rw [l,numericMomentEntry,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a _
  have ev : tinyDet k (Matrix.of fun c d =>
      rawEntryValue b (x a) (E.axis i c) (E.axis t d))=P.eval (x a) := by
    dsimp only [P]
    rw [rawMinor_on_axes]
    let A : Matrix (Fin k) (Fin k) R[X] :=
      Matrix.of (fun c d => rawResolvent b (E.axis i c) (E.axis t d))
    change _=(tinyDet k A).eval (x a)
    rw [tinyDet_eq_det k A,tinyDet_eq_det]
    change _=(evalRingHom (x a)) A.det
    rw [(evalRingHom (x a)).map_det]
    congr 1
    apply Matrix.ext
    intro c d
    exact rawEntryValue_exact _ _ _ _
  rw [ev,numericWeight_exact]
  rfl

end RKCert.Compound
