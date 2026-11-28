import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10ThreePairChronologyScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

def N (x i j : R) : R := 3*x^2-4*(i+j)*x+6*i*j

theorem freeTapDeterminant (s t j k : R) :
    N s s k * N t s j - N s s j * N t s k =
    -6*s*(j-k)*(t-s)^2 := by
  unfold N
  grind

theorem freeTargetKernel (s t j k a b : R)
    (first : N s s k*a+N s s j*b=0)
    (second : N t s k*a+N t s j*b=0) :
    (-6*s*(j-k)*(t-s)^2)*a=0 ∧ (-6*s*(j-k)*(t-s)^2)*b=0 := by
  rw [← freeTapDeterminant]
  constructor
  · calc
      _ = N t s j*(N s s k*a+N s s j*b)
          - N s s j*(N t s k*a+N t s j*b) := by clear first second; grind
      _ = 0 := by rw [first,second]; grind
  · calc
      _ = N s s k*(N t s k*a+N t s j*b)
          - N t s k*(N s s k*a+N s s j*b) := by clear first second; grind
      _ = 0 := by rw [first,second]; grind

theorem foldTwoOpposed (a b w u : R) :
    (a*w+b*(-w)=(a-b)*w) ∧ (a*u+b*(-u)=(a-b)*u) := by
  constructor <;> grind

theorem blindTapFactors (a b u v : R)
    (p1 : a*u+b*v=0) (p2 : a^2*u+b^2*v=0) :
    a*(a-b)*u=0 ∧ b*(b-a)*v=0 := by
  constructor
  · calc
      _ = (a^2*u+b^2*v)-b*(a*u+b*v) := by clear p1 p2; grind
      _ = 0 := by rw [p1,p2]; grind
  · calc
      _ = (a^2*u+b^2*v)-a*(a*u+b*v) := by clear p1 p2; grind
      _ = 0 := by rw [p1,p2]; grind

end Ring

section Field
variable {F : Type} [Field F]

theorem freeTargetExit (s t j k a b : F)
    (six : (6:F) ≠ 0) (snz : s ≠ 0) (st : t ≠ s) (jk : j ≠ k)
    (first : N s s k*a+N s s j*b=0)
    (second : N t s k*a+N t s j*b=0) :
    a=0 ∧ b=0 := by
  have hd : (-6*s*(j-k)*(t-s)^2 : F) ≠ 0 := by grind
  obtain ⟨ha,hb⟩ := freeTargetKernel s t j k a b first second
  exact ⟨by grind,by grind⟩

theorem blindTwoTaps (a b u v : F) (an : a ≠ 0) (bn : b ≠ 0) (ab : a ≠ b)
    (p1 : a*u+b*v=0) (p2 : a^2*u+b^2*v=0) : u=0 ∧ v=0 := by
  obtain ⟨hu,hv⟩ := blindTapFactors a b u v p1 p2
  exact ⟨by grind,by grind⟩

end Field
end RKResearch.Certified.ERK10ThreePairChronologyScalars

#print axioms RKResearch.Certified.ERK10ThreePairChronologyScalars.freeTapDeterminant
#print axioms RKResearch.Certified.ERK10ThreePairChronologyScalars.foldTwoOpposed
#print axioms RKResearch.Certified.ERK10ThreePairChronologyScalars.freeTargetExit
#print axioms RKResearch.Certified.ERK10ThreePairChronologyScalars.blindTwoTaps
