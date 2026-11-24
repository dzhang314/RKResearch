module
public import RKCert.SplitFactorGate
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section
namespace RKCert.PortRank
open Polynomial Matrix
open RKCert.FixedFactor

/-- A column of the cleared global primitive with 429-scaled root coordinates. -/
def globalEntry {R : Type*} [CommRing R] (a:ℕ→R) (k j:ℕ) : R :=
  ∑i∈Finset.range 6, (360360/(k+i+j+1):ℕ)*a i*(429:R)^(k+i+j+1)

/-- A column of either cleared local primitive. -/
def localEntry {R : Type*} [CommRing R] (u:R) (k j:ℕ) : R :=
  (360360/(k+j+1):ℕ)*u^(k+j+1)

/-- A single fixed universal square subsystem of the seven paid equations.
Rows are global 0 minus global 1, global 2, global 3, local 1, local 2. -/
def portMatrix {R : Type*} [CommRing R] (a:ℕ→R) (u:R) : Matrix (Fin 5) (Fin 5) R :=
  fun i j=>match i.val with
    | 0=> globalEntry a 0 j.val-globalEntry a 1 j.val
    | 1=> globalEntry a 2 j.val
    | 2=> globalEntry a 3 j.val
    | 3=> localEntry u 1 j.val
    | _=> localEntry u 2 j.val

noncomputable def portDet {R : Type*} [CommRing R] (P:R[X]) (u:R) : R :=
  (portMatrix P.coeff u).det

theorem map_global {R S : Type*} [CommRing R] [CommRing S] (φ:R→+*S) (a:ℕ→R) (k j:ℕ) :
    φ (globalEntry a k j)=globalEntry (fun i=>φ (a i)) k j := by
  have h : φ (429:R)=429 := map_natCast φ 429
  simp [globalEntry,h]

theorem map_portDet {R S : Type*} [CommRing R] [CommRing S] (φ:R→+*S) (P:R[X]) (w:R) :
    φ (portDet P w)=portDet (P.map φ) (φ w) := by
  rw [portDet,φ.map_det,portDet]
  congr 1
  ext i j
  have hcf : (fun i=>φ (P.coeff i))=(P.map φ).coeff := by funext i; rw [coeff_map]
  fin_cases i <;> simp [portMatrix,Matrix.map_apply,map_global,localEntry,hcf]

/-- The standard Laplace recurrence, written executably so that the 693
finite arithmetic checks reduce in the Lean kernel. -/
def smallDet {R : Type*} [CommRing R] :
    (n:ℕ) → Matrix (Fin n) (Fin n) R → R
  | 0,_=>1
  | n+1,M=>∑ j:Fin (n+1), (-1:R)^j.val*M 0 j*smallDet n (M.submatrix Fin.succ j.succAbove)

theorem smallDet_eq_det {R : Type*} [CommRing R] (n:ℕ) (M:Matrix (Fin n) (Fin n) R) :
    smallDet n M=M.det := by
  induction n with
  | zero => simp [smallDet]
  | succ n ih => rw [smallDet,Matrix.det_succ_row_zero]; simp only [ih]

theorem portDet_product {R : Type*} [Field R] (l:List R) (u:R) :
    portDet (linearProduct id l) u=smallDet 5 (portMatrix (coeffs l) u) := by
  simp only [portDet,smallDet_eq_det]
  congr 2
  funext i
  exact coeff_product l i

end RKCert.PortRank
