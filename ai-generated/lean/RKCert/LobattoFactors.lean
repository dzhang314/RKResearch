module
public import RKCert.LobattoFactorTables
public import RKCert.FactorPrimitiveScale
public import RKCert.TerminalLobatto

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K : Type*} [Field K] [CharZero K]

theorem degree_lobatto7 : (lobatto (K:=K) 7).natDegree=7 := by
  apply le_antisymm (lobatto_degree (by decide))
  apply le_natDegree_of_ne_zero
  rw [lobatto_coeff]
  norm_num [lobattoCoeff,Polynomial.coeff_shiftedLegendre,Nat.choose]

/-- Clearing the leading coefficient turns the native signed shifted-Legendre
derivative into a monic integral polynomial on rescaled root coordinates. -/
theorem scaled_lobatto7 : (lobatto (K:=K) 7).scaleRoots (429:K) =
    C (24024:K)*((X*grid7).map (Int.castRingHom K)) := by
  ext i
  cases i with
  | zero =>
    rw [coeff_scaleRoots,lobatto_coeff,lobatto_coeff_zero,zero_mul,coeff_C_mul,coeff_map,
      coeff_X_mul_zero,map_zero,mul_zero]
  | succ n =>
    rw [coeff_scaleRoots,degree_lobatto7,coeff_C_mul,coeff_map,coeff_X_mul]
    by_cases hn : n≤6
    · interval_cases n <;> norm_num [lobatto_coeff,lobattoCoeff,Polynomial.coeff_shiftedLegendre,
        Nat.choose,grid7,coeff_horner,digits7,readCoeff]
    · rw [coeff_eq_zero_of_natDegree_lt (show (lobatto (K:=K) 7).natDegree<n+1 by
            rw [degree_lobatto7]; omega),zero_mul,
          coeff_eq_zero_of_natDegree_lt (show grid7.natDegree<n by rw [degree_grid7]; omega),
          map_zero,mul_zero]

/-- For every divisor P of the degree-7 terminal Lobatto polynomial of degree
at most 4, its first weighted primitive is nonzero at every nonzero Lobatto
node. No root-omission, second moment, order or embedding into ℝ is needed. -/
theorem lobatto7_first_moment {P : K[X]} {u : K} (hdiv : P ∣ lobatto 7)
    (hdegree : P.natDegree≤4) (hu : u≠0) (hroot : (lobatto 7).eval u=0) :
    (primitive (X*P)).eval u≠0 := by
  have hG : lobatto (K:=K) 7≠0 := by
    intro h
    have e:=degree_lobatto7 (K:=K)
    rw [h,natDegree_zero] at e
    omega
  exact native_from_scaled _ grid7 (429:K) (24024:K) (by norm_num) (by norm_num)
    scaled_lobatto7 420 4 (by intro i hi; interval_cases i <;> decide)
    gate_grid7 P u (ne_zero_of_dvd_ne_zero hG hdiv) hdiv hdegree hu hroot

theorem degree_lobatto8 : (lobatto (K:=K) 8).natDegree=8 := by
  apply le_antisymm (lobatto_degree (by decide))
  apply le_natDegree_of_ne_zero
  rw [lobatto_coeff]
  norm_num [lobattoCoeff,Polynomial.coeff_shiftedLegendre,Nat.choose]

/-- Clearing the leading coefficient turns the native signed shifted-Legendre
derivative into a monic integral polynomial on rescaled root coordinates. -/
theorem scaled_lobatto8 : (lobatto (K:=K) 8).scaleRoots (1430:K) =
    C (102960:K)*((X*grid8).map (Int.castRingHom K)) := by
  ext i
  cases i with
  | zero =>
    rw [coeff_scaleRoots,lobatto_coeff,lobatto_coeff_zero,zero_mul,coeff_C_mul,coeff_map,
      coeff_X_mul_zero,map_zero,mul_zero]
  | succ n =>
    rw [coeff_scaleRoots,degree_lobatto8,coeff_C_mul,coeff_map,coeff_X_mul]
    by_cases hn : n≤7
    · interval_cases n <;> norm_num [lobatto_coeff,lobattoCoeff,Polynomial.coeff_shiftedLegendre,
        Nat.choose,grid8,coeff_horner,digits8,readCoeff]
    · rw [coeff_eq_zero_of_natDegree_lt (show (lobatto (K:=K) 8).natDegree<n+1 by
            rw [degree_lobatto8]; omega),zero_mul,
          coeff_eq_zero_of_natDegree_lt (show grid8.natDegree<n by rw [degree_grid8]; omega),
          map_zero,mul_zero]

/-- For every divisor P of the degree-8 terminal Lobatto polynomial of degree
at most 5, its first weighted primitive is nonzero at every nonzero Lobatto
node. No root-omission, second moment, order or embedding into ℝ is needed. -/
theorem lobatto8_first_moment {P : K[X]} {u : K} (hdiv : P ∣ lobatto 8)
    (hdegree : P.natDegree≤5) (hu : u≠0) (hroot : (lobatto 8).eval u=0) :
    (primitive (X*P)).eval u≠0 := by
  have hG : lobatto (K:=K) 8≠0 := by
    intro h
    have e:=degree_lobatto8 (K:=K)
    rw [h,natDegree_zero] at e
    omega
  exact native_from_scaled _ grid8 (1430:K) (102960:K) (by norm_num) (by norm_num)
    scaled_lobatto8 420 5 (by intro i hi; interval_cases i <;> decide)
    gate_grid8 P u (ne_zero_of_dvd_ne_zero hG hdiv) hdiv hdegree hu hroot

end RKCert.FixedFactor
