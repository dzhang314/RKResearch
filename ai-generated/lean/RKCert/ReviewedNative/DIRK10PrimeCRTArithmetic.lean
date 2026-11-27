module

@[expose] public section

/-! Arithmetic receipts for the common modulus. This module only uses core Lean. -/

namespace RKResearch.Certified.DIRK10PrimeCRT

def modulus : Nat := 493171545720458172452176512475299940647302199454377045107793303879169620903625874853054017
def primes : List Nat := [59, 73, 127, 149, 191, 199, 283, 373, 419, 461, 467, 521, 563, 601, 739, 761, 773, 811, 829, 857, 863, 919, 947, 967, 1031, 1171, 1193, 1319, 1409, 1481, 1487, 1499]
def factorModuli : List Nat := [3481, 73, 127, 149, 191, 199, 283, 373, 419, 461, 467, 521, 563, 601, 739, 761, 773, 811, 829, 857, 863, 919, 947, 967, 1031, 1171, 1193, 1319, 1409, 1481, 1487, 1499]

theorem factorProduct : factorModuli.prod=modulus := by decide +kernel

theorem supportedDivisors :
    ((3481::primes).all fun p => decide (modulus % p = 0)) = true := by decide +kernel

theorem divides_of_mem {p : Nat} (h : p ∈ 3481::primes) : p ∣ modulus :=
  Nat.dvd_iff_mod_eq_zero.mpr (of_decide_eq_true (List.all_eq_true.mp supportedDivisors p h))

theorem prime_divides {p : Nat} (h : p ∈ primes) : p ∣ modulus :=
  divides_of_mem (List.mem_cons_of_mem _ h)

theorem squared_59_divides : (59^2:Nat) ∣ modulus :=
  divides_of_mem (by decide)

#print axioms factorProduct
#print axioms divides_of_mem

end RKResearch.Certified.DIRK10PrimeCRT
