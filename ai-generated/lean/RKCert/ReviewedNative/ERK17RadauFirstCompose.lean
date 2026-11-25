module

public import RKCert.ReviewedNative.ERK17ContrastCount
public import RKCert.ReviewedNative.NativeRadauFirstRecognition

@[expose] public section

/-! # Literal first-Radau gate from a single chosen conjugate cut

The final pure cut can be supplied at the least real root or at a root
selected by a finite residue place. No scalar solve or extra row premise
is imported by this dispatch. -/
namespace RKResearch.Certified.ERK17

open Polynomial RKResearch.Certified.Graded
open RKResearch.Certified.Graded.NativeRootTransport
open RKCert.ReviewedNative.WeightXEight

/-- Exact interface for a standalone scalar exclusion at one chosen
conjugate root. The eight native tests and the actual first primitive
are unchanged; no real split of the source cubic is required. -/
theorem native_radau_first_of_chosen_root
    {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    (split : (rationalPolynomial.map (algebraMap ℚ E)).Splits)
    {v : E} (rootV : (rationalPolynomial.map (algebraMap ℚ E)).IsRoot v)
    (cut : ∀ Q N : E[X], Q.Monic → N.Monic →
      Q.natDegree=5 → N.natDegree=3 →
      Q*N=rationalPolynomial.map (algebraMap ℚ E) → N.IsRoot v →
      (primitive (X*Q)).eval v≠0) : RadauFirstGate K := by
  intro Q N u qn qd nn nd root _ test localZero
  obtain ⟨Q₀,N₀,qm,nm,q5,n3,prod,root₀,zero₀⟩ :=
    monic_window_of_first_zero qn qd nn nd root test localZero
  obtain ⟨Q',N',qM,nM,qD,nD,factor,newRoot,newZero⟩ :=
    transport_first_primitive_zero rationalPolynomial rational_monic rational_irreducible
      qm nm prod root₀ zero₀ split rootV
  exact cut Q' N' qM nM (qD.trans q5) (nD.trans n3) factor newRoot newZero

end RKResearch.Certified.ERK17
