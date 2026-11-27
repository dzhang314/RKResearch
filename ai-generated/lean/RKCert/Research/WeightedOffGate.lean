import Lean

/-!
# Four-budget weighted order-nine off-state gates

This standalone core file checks the literal five-site Hadamard step, the
local second/third tap constraints and the fixed shift-two Radau arithmetic.
The accompanying proof explains which actual rooted columns, ranks and
moment equations provide the premises; this file is not an RK stage bound.
-/
namespace RKResearch.WeightedOffGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem cancel {a b c : K} (h : a ≠ 0) (e : a * b = a * c) : b = c := by
  have h' := congrArg (fun x => a⁻¹ * x) e
  simpa [← Semiring.mul_assoc, Field.inv_mul_cancel h, Semiring.one_mul] using h'

private theorem mulNonzero {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun hz => hb ((Field.of_mul_eq_zero hz).resolve_left ha)

def tail (i : Fin 5) : K := if i = 4 then 1 else 0

/-- Multiplying an actual late vector by a quadratic defect cannot produce
any late product when the middle clock subdiagonal is nonzero. The hypotheses
expose the rooted subspace span, two annihilating taps, and the actual
triangular pivots needed for the proof. Indices 2 and 3 are physical
stages 10 and 11 in the 12-stage application. -/
theorem eliminateHadamard
    (Y v η₁ η₂ η₃ defect : Fin 5 → K)
    (y z y₂ k₀ k₂ q₀ q₁ μ₀ μ₁ μ₂ μ₃ T a b c d : K)
    (hz : z ≠ 0) (hread : μ₁ ≠ 0) (hT : T ≠ 0)
    (h2pivot : η₂ 2 ≠ 0) (h3pivot : η₃ 3 ≠ 0) (h3zero : η₃ 2 = 0)
    (clock₀ : ∀ i, (Y i-y)*v i = k₀ * tail i)
    (clock₁ : ∀ i, (Y i-y)*η₁ i = -η₂ i)
    (clock₂ : ∀ i, (Y i-y)*η₂ i = (y₂-y)*η₂ i + z*η₃ i + k₂*tail i)
    (spanProduct : ∀ i, v i * defect i = a*v i+b*η₁ i+c*η₂ i+d*tail i)
    (pure₁ : a*μ₁+b*μ₂+c*μ₃ = 0)
    (pure₀ : a*μ₀+b*q₀+c*q₁+d*T = 0) :
    ∀ i, v i * defect i = 0 := by
  have clockProd (i : Fin 5) :
      (-b+(y₂-y)*c)*η₂ i+(z*c)*η₃ i =
          (k₀*defect i-a*k₀-c*k₂-d*(Y i-y))*tail i := by
    have hm := congrArg (fun x => (Y i-y)*x) (spanProduct i)
    rw [← Semiring.mul_assoc (Y i-y) (v i) (defect i), clock₀ i] at hm
    simp only [Semiring.left_distrib] at hm
    rw [CommSemiring.mul_left_comm (Y i-y) a (v i), clock₀ i,
        CommSemiring.mul_left_comm (Y i-y) b (η₁ i), clock₁ i,
        CommSemiring.mul_left_comm (Y i-y) c (η₂ i), clock₂ i] at hm
    grind
  have h₂ := clockProd 2
  have h₃ := clockProd 3
  have t₂ : tail (K:=K) 2 = 0 := by
    unfold tail
    exact ite_eq_right (by decide)
  have t₃ : tail (K:=K) 3 = 0 := by
    unfold tail
    exact ite_eq_right (by decide)
  rw [t₂, h3zero] at h₂
  have aux₂ : (-b+(y₂-y)*c)*η₂ 2 = 0 := by grind
  have p₂ := (Field.of_mul_eq_zero aux₂).resolve_right h2pivot
  rw [t₃,p₂] at h₃
  have aux₃ : (z*c)*η₃ 3 = 0 := by grind
  have cz := (Field.of_mul_eq_zero
    ((Field.of_mul_eq_zero aux₃).resolve_right h3pivot)).resolve_left hz
  have bz : b = 0 := by grind
  have az' : a*μ₁=0 := by grind
  have az := (Field.of_mul_eq_zero az').resolve_right hread
  have dz' : d*T=0 := by grind
  have dz := (Field.of_mul_eq_zero dz').resolve_right hT
  intro i
  have hi := spanProduct i
  grind

/-- An eigenvector at the second physical site cannot have both the second
tap and the grade-six annihilator read zero. The latter would put it in the
late span with no third-shift component; the two clock equations below are
the corresponding coefficient requirements. -/
theorem rejectDualZero
    (m a y y₂ T U b₁ b₂ : K) (hT : T ≠ 0) (hb₁ : b₁ ≠ 0)
    (highest : U = a*T) (leadClock : a*y = m+4)
    (eigen₂ : (y₂-y)*b₂ = b₁)
    (eigen₃ : (m+2-a*y₂)*b₂ = 0)
    (zeroTap₂ : b₁*U+b₂*T = 0) :
    False := by
  have hB : b₂ ≠ 0 := by
    intro h
    apply hb₁
    grind
  have high₂ := (Field.of_mul_eq_zero eigen₃).resolve_right hB
  have tap₂ : T*(b₂+a*b₁) = T*0 := by grind
  have tap₂' := cancel hT tap₂
  have eigen := congrArg (fun x => a*x) eigen₂
  apply hB
  grind

/-- At the resonant third clock, the second site's second and third
taps obey the fixed one-half relation in the normalized cyclic chart. -/
theorem halfRead
    (m a y y₂ T U b₁ b₂ : K)
    (highest : U = a*T) (leadClock : a*y = m+4)
    (resonant : a*y₂ = m+2)
    (eigen₂ : (y₂-y)*b₂ = b₁) :
    2*(b₁*U+b₂*T) = b₁*U := by
  have e := congrArg (fun x => a*x) eigen₂
  have h : a*b₁ = -2*b₂ := by grind
  have h' := congrArg (fun x => T*x) h
  grind

/-- Physical support confines the two reads of v to these indicated sites.
If the first site's second tap vanishes, the third tap at the same site
is forced nonzero. No signing of the weights is used. -/
theorem nonzeroThirdAtFirst
    (m a U V T v₀ v₁ ρ₁ σ₀ σ₁ b₁ : K)
    (aN : a ≠ 0) (uN : U ≠ 0) (pN : m+2 ≠ 0)
    (highest : U = a*T)
    (moment : (m+4)*V = (m+3)*a*U)
    (read₂ : V = v₁*ρ₁)
    (read₃ : U = v₀*σ₀+v₁*σ₁)
    (twoAtSecond : 2*ρ₁ = b₁*U)
    (threeAtSecond : σ₁ = b₁*T) :
    σ₀ ≠ 0 := by
  have pay := congrArg (fun x => v₁*x) twoAtSecond
  have sc := congrArg (fun x => a*x) read₃
  have eq : 2*V = a*(U-v₀*σ₀) := by grind
  have eq' := congrArg (fun x => (m+4)*x) eq
  have m' := congrArg (fun x => 2*x) moment
  have e : a*((m+4)*v₀*σ₀+(m+2)*U) = a*0 := by grind
  have e' := cancel aN e
  intro z
  apply mulNonzero pN uN
  grind

/-- Shift-two anchored orthogonal quartic, in physical clock X. -/
def radau (x : K) : K := 66*x^4-120*x^3+72*x^2-16*x+1
def g (y : K) : K := 66*y^4-144*y^3+108*y^2-32*y+3
def h (y : K) : K := 352*y^4-1152*y^3+1296*y^2-576*y+81
def bezoutG (y : K) : K := 7243765760*y^3-19604901120*y^2+15591140352*y-3132850032
def bezoutH (y : K) : K := -1358206080*y^3+2194239600*y^2-984229056*y+116843869

theorem reflectedRadau (y : K) : radau (1-y) = g y := by
  unfold radau g
  grind

theorem scaledRadau (y z : K) (e : 3*z = 2*y) : 27*g z = h y := by
  calc
    27*g z = 22*(3*z)^4-144*(3*z)^3+324*(3*z)^2-288*(3*z)+81 := by
      unfold g
      grind
    _ = 22*(2*y)^4-144*(2*y)^3+324*(2*y)^2-288*(2*y)+81 := by rw [e]
    _ = h y := by
      unfold h
      grind

theorem radauBezout (y : K) : bezoutG y*g y+bezoutH y*h y = 65803293 := by
  unfold bezoutG bezoutH g h
  grind

/-- Over any field in which the displayed Bézout constant is nonzero,
two shift-two anchored Radau clocks cannot have reflected ratio 2/3. -/
theorem reflectedPairImpossible (y z : K) (paid : (65803293 : K) ≠ 0)
    (e : 3*z = 2*y) (g₁ : radau (1-y) = 0) (g₂ : radau (1-z) = 0) : False := by
  have gz : g z = 0 := (reflectedRadau z).symm.trans g₂
  have gy : g y = 0 := (reflectedRadau y).symm.trans g₁
  have hz : h y = 0 := by
    rw [←scaledRadau y z e, gz, Semiring.mul_zero]
  apply paid
  have b := radauBezout y
  rw [gy,hz,Semiring.mul_zero,Semiring.mul_zero,Semiring.add_zero] at b
  exact b.symm

def beta2Moment (k : Nat) : Rat := 1/(((k+1)*(k+2)*(k+3) : Nat) : Rat)

/-- Orthogonality of X times radau against all four required monomials. -/
theorem radauOrthogonality : ∀ i : Fin 4,
    66*beta2Moment (i.val+5)-120*beta2Moment (i.val+4)+72*beta2Moment (i.val+3)
      -16*beta2Moment (i.val+2)+beta2Moment (i.val+1)=0 := by
  decide +kernel

end RKResearch.WeightedOffGate
#print axioms RKResearch.WeightedOffGate.eliminateHadamard
#print axioms RKResearch.WeightedOffGate.rejectDualZero
#print axioms RKResearch.WeightedOffGate.halfRead
#print axioms RKResearch.WeightedOffGate.nonzeroThirdAtFirst
#print axioms RKResearch.WeightedOffGate.reflectedPairImpossible
#print axioms RKResearch.WeightedOffGate.radauOrthogonality
