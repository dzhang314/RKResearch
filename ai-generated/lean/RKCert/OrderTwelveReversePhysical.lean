module
public import RKCert.OrderTwelveReverseChart
public import RKCert.ERKGradeFive

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired Module
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- Every genuine order-twelve explicit tableau with at most 17 stages
has the forced reverse chart; no auxiliary saturation or support hypothesis. -/
theorem actual_reverse_seven_nine {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hsize:s+1≤17) :
    ReverseSevenNine A b := by
  have hf := grade_five_surplus ha (explicit_separated ha ho (q:=5) (by decide) (by omega))
  exact reverse_seven_nine ha ho (saturation ha ho hf hsize)

end RKCert.Paired.OrderTwelve
