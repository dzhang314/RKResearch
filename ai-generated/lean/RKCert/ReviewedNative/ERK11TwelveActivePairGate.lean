/-! Portable ring arithmetic for the twelve-active two-pair reduction. -/
namespace RKResearch.ERK11TwelveActivePairGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem recoverSecondResponse (b c f g : R) :
    let ν := b*f+c*g
    let μ := b*f^2+c*g^2
    let τ := b*f^3+c*g^3
    μ-f*ν = c*g*(g-f) ∧ (μ-f*ν)*g=τ-f*μ := by
  dsimp
  grind

theorem ordinaryResponseHullPivot (b c f g : R) :
    (b+c)*(b*f^2+c*g^2)-(b*f+c*g)^2 = b*c*(f-g)^2 := by
  grind

theorem twoNodeVariance (i₀ i₁ i₂ p q : R)
    (h : i₂-(p+q)*i₁+p*q*i₀=0) :
    (p*i₀-i₁)*(q*i₀-i₁) = -(i₀*i₂-i₁^2) := by
  have hi : i₂=(p+q)*i₁-p*q*i₀ := by grind
  rw [hi]
  grind

theorem clearCenteredMark (h c₁ c₂ i₀ i₁ i₂ x z : R)
    (hx : h*x=c₂) (hz : h*z=c₁)
    (hm : i₂-(x+z)*i₁+x*z*i₀=0) :
    h^2*i₂-h*i₁*(c₁+c₂)+i₀*c₁*c₂=0 := by
  rw [← hx,← hz]
  calc
    h^2*i₂-h*i₁*(h*z+h*x)+i₀*(h*z)*(h*x) =
      h^2*(i₂-(x+z)*i₁+x*z*i₀) := by grind
    _ = 0 := by rw [hm]; grind

def aliasSextic (a : R) : R :=
  680625*a^6-2214300*a^5+2982540*a^4-2140908*a^3+
    869470*a^2-190365*a+17640

theorem centeredAliasNumerator (a : R) :
    let h := 25*a^2-25*a+7
    let c₁ := 1100*a^2-1155*a+336
    let c₂ := 825*a^2-924*a+280
    let i₀ := 12*a^2-15*a+5
    let i₁ := 15*a^2-20*a+7
    let i₂ := 55*a^2-77*a+28
    396*h^2*i₂-33*h*i₁*(c₁+c₂)+i₀*c₁*c₂=aliasSextic a := by
  dsimp [aliasSextic]
  grind

def homSextic (u v : R) : R :=
  680625*u^6-2214300*u^5*v+2982540*u^4*v^2-2140908*u^3*v^3+
    869470*u^2*v^4-190365*u*v^5+17640*v^6

theorem aliasHalfFirst (t : R) :
    homSextic t (2*(1+t)) =
    1128960+682080*t+387520*t^2+181216*t^3+35088*t^4+11368*t^5+3721*t^6 := by
  unfold homSextic
  grind

theorem aliasHalfSecond (t : R) :
    homSextic (5+8*t) (10*(1+t)) =
    58140625+451575000*t+1577370000*t^2+2686124000*t^3+
      2230776000*t^4+384636000*t^5+152224000*t^6 := by
  unfold homSextic
  grind

theorem aliasExteriorRight (t : R) :
    homSextic (4+t) 5 =
    2378500+5507375*t+17992750*t^2+25162500*t^3+
       16483500*t^4+5263500*t^5+680625*t^6 := by
  unfold homSextic
  grind

end RKResearch.ERK11TwelveActivePairGate
#print axioms RKResearch.ERK11TwelveActivePairGate.recoverSecondResponse
#print axioms RKResearch.ERK11TwelveActivePairGate.ordinaryResponseHullPivot
#print axioms RKResearch.ERK11TwelveActivePairGate.twoNodeVariance
#print axioms RKResearch.ERK11TwelveActivePairGate.clearCenteredMark
#print axioms RKResearch.ERK11TwelveActivePairGate.centeredAliasNumerator
#print axioms RKResearch.ERK11TwelveActivePairGate.aliasHalfFirst
#print axioms RKResearch.ERK11TwelveActivePairGate.aliasHalfSecond
#print axioms RKResearch.ERK11TwelveActivePairGate.aliasExteriorRight
