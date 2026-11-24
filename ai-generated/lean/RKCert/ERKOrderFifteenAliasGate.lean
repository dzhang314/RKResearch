module
public import RKCert.ERKOrderFifteenChart
public import RKCert.LobattoFactors

@[expose] public section

/-! # The marked order-15 alias uses the existing native Lobatto obstruction

The shared fixed-factor theorem is stronger than the two-moment alias
test: it handles an arbitrary cubic divisor over the original field,
without explicit splitting of its roots and with only the first moment.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Terminal RKCert.FixedFactor Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem dx6_native_lobatto : (dx6 : K[X])=lobatto 7 := by
  ext n
  by_cases h:n≤7
  · interval_cases n <;>
      norm_num [dx6_coeff,lobatto_coeff,lobattoCoeff,Polynomial.coeff_shiftedLegendre,Nat.choose]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [dx6_degree];omega),
      coeff_eq_zero_of_natDegree_lt (by rw [degree_lobatto7];omega)]

theorem fixed_alias_first_moment {d : ℕ} {G P : K[X]}
    (hg : OddSevenMesh G d) (gd : G.natDegree≤7) (ng : G≠0)
    (pf : P∣G) (pd : P.natDegree≤4) {u : K} (un : u≠0) (ug : G.eval u=0) :
    (primitive (X*P)).eval u≠0 := by
  obtain ⟨_,_,t,tn,eq⟩ := odd_seven_alias_form hg gd ng
  rw [dx6_native_lobatto,smul_eq_C_mul] at eq
  have unit : IsUnit (C t) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr tn)
  have hdiv : P∣lobatto 7 := (unit.dvd_mul_left).mp (eq ▸ pf)
  rw [eq,eval_mul,eval_C] at ug
  exact lobatto7_first_moment hdiv pd un ((mul_eq_zero.mp ug).resolve_left tn)

variable {s d r : ℕ} {A : Fin (s+1)→Fin (s+1)→K}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

theorem OddSevenChart.alias_first_moment (C : OddSevenChart A d 6 r U w G)
    (P : K[X]) (pf : P∣G) (pd : P.natDegree≤4)
    {u : K} (un : u≠0) (ug : G.eval u=0) :
    (primitive (X*P)).eval u≠0 := by
  have gd : G.natDegree=7 := C.meshDegree
  exact fixed_alias_first_moment C.mesh gd.le
    (fun e=>by rw [e,natDegree_zero] at gd; omega) pf pd un ug

end RKCert.Paired.FiniteMidpoint
