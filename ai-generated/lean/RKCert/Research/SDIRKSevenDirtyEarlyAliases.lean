module

public import RKCert.Research.SDIRKSixTailScalarObstruction
import all RKCert.Research.SDIRKSixTailScalarObstruction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

public section

/-! # Early ghost aliases in the reflection branch

The raw reverse suffix hands off precisely one new Laguerre bridge
to the previous rational scalar obstruction. The middle (sixth)
active node is assumed not to be the ghost alias: this is exactly
what permits replacing its own error by the grouped tail residue.
-/
namespace RKResearch.Certified.SDIRKSevenDirtyEarlyAliases
open SDIRKSixTailScalarObstruction
noncomputable section

def M (z s t w : ℚ) (k : ℕ) : ℚ :=
  z^(k+3)/((k:ℚ)+4)+s*z^(k+2)/((k:ℚ)+3)+
  t*z^(k+1)/((k:ℚ)+2)+w*z^k/((k:ℚ)+1)

def Q (z s t c : ℚ) (k : ℕ) : ℚ :=
  z^(k+2)/((k:ℚ)+3)+(s+c)*z^(k+1)/((k:ℚ)+2)+
  (t+s*c+c^2)*z^k/((k:ℚ)+1)

def lag (c : ℚ) : ℚ := c^3-9*c^2+18*c-6
def ρ (u : ℚ) : ℚ := u*(4-u)
def cut (u c : ℚ) : ℚ := (c-1)*(c-u)*(c-(4-u))

def ku (m : ℕ→ℚ) (u : ℚ) : ℚ := m 2-(5-u)*m 1+(4-u)*m 0
def kv (m : ℕ→ℚ) (u : ℚ) : ℚ := m 2-(u+1)*m 1+u*m 0
def klast (m : ℕ→ℚ) (u : ℚ) : ℚ := m 2-4*m 1+ρ u*m 0

def kc (m : ℕ→ℚ) (u c q₀ : ℚ) : ℚ :=
  m 2+(c-5)*m 1+(c^2-5*c+4+ρ u)*m 0+cut u c*q₀

/-- Necessary normalized scalar conditions from a coalesced ghost at
one of the first two active sites, with a distinct sixth-stage clock. -/
structure ReflectionAlias (z s t w c u : ℚ) : Prop where
  zn : z≠0
  un₁ : u≠1
  un₂ : u≠2
  un₃ : u≠3
  distinct_c : cut u c≠0
  root : c^3+s*c^2+t*c+w=0
  twin : ku (M z s t w) u=kv (M z s t w) u
  terminal : (2-ρ u)*ku (M z s t w) u+klast (M z s t w) u=0
  quadrature : M z s t w 3-5*M z s t w 2+(4+ρ u)*M z s t w 1-ρ u*M z s t w 0=0
  fourth : lag c*kc (M z s t w) u c (Q z s t c 0)+
    (4*(2-ρ u)+(2+ρ u)*(c-1))*ku (M z s t w) u=0

/-- The reflection ghost alias would imply the rootless prior
exceptional scalar branch, with no condition on the helper tap. -/
theorem reflection_alias_impossible {z s t w c u : ℚ}
    (h : ReflectionAlias z s t w c u) : False := by
  let m := M z s t w
  have az : (u-2)*(m 1-m 0)=0 := by
    have eq := h.twin
    unfold ku kv at eq
    linear_combination eq/2
  have m1 : m 1=m 0 := sub_eq_zero.mp ((mul_eq_zero.mp az).resolve_left (sub_ne_zero.mpr h.un₂))
  have r0 : 3-ρ u≠0 := by
    have e : 3-ρ u=(u-1)*(u-3) := by unfold ρ; ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.mpr h.un₁) (sub_ne_zero.mpr h.un₃)
  have bz : (3-ρ u)*(m 2-2*m 0)=0 := by
    have eq := h.terminal
    change (2-ρ u)*ku m u+klast m u=0 at eq
    unfold ku klast at eq
    rw [m1] at eq
    linear_combination eq
  have m2 : m 2=2*m 0 := sub_eq_zero.mp ((mul_eq_zero.mp bz).resolve_left r0)
  have m3 : m 3=6*m 0 := by
    have eq := h.quadrature
    change m 3-5*m 2+(4+ρ u)*m 1-ρ u*m 0=0 at eq
    rw [m1,m2] at eq
    linear_combination eq
  have w4 : cut u c*(lag c*Q z s t c 0+(c^2-8*c+11)*m 0)=0 := by
    have e := h.fourth
    change lag c*kc m u c (Q z s t c 0)+(4*(2-ρ u)+(2+ρ u)*(c-1))*ku m u=0 at e
    unfold ku kc at e
    rw [m1,m2] at e
    simp only [cut,ρ,lag] at e ⊢
    linear_combination e
  have g := (mul_eq_zero.mp w4).resolve_left h.distinct_c
  have q : Q z s t c 3-9*Q z s t c 2+18*Q z s t c 1-6*Q z s t c 0 =
      lag c*Q z s t c 0+(c^2-8*c+11)*m 0 := by
    have v : Q z s t c 3-9*Q z s t c 2+18*Q z s t c 1-6*Q z s t c 0 =
        lag c*Q z s t c 0+m 2+(c-9)*m 1+(c^2-9*c+18)*m 0 := by
      dsimp [m]
      unfold Q M lag
      norm_num
      linear_combination -(z^2/3+(c-9)*z/2+(c^2-9*c+18))*h.root
    rw [v,m1,m2]
    ring
  have q0 := q.trans g
  apply exceptional_branch_impossible h.zn ?_ ?_ ?_ h.root ?_
  · change -15*s*z^3+20*s*z^2-20*t*z^2+30*t*z-30*w*z+60*w-12*z^4+15*z^3=0
    dsimp [m] at m1
    unfold M at m1
    norm_num at m1
    linear_combination -60*m1
  · change 12*s*z^4-60*s*z^3+40*s*z^2+15*t*z^3-80*t*z^2+60*t*z+
      20*w*z^2-120*w*z+120*w+10*z^5-48*z^4+30*z^3=0
    dsimp [m] at m1 m2
    unfold M at m1 m2
    norm_num at m1 m2
    linear_combination -240*m1+60*m2
  · change -70*s*z^5+756*s*z^4-1890*s*z^3+840*s*z^2-84*t*z^4+945*t*z^3-
      2520*t*z^2+1260*t*z-105*w*z^3+1260*w*z^2-3780*w*z+2520*w-60*z^6+
      630*z^5-1512*z^4+630*z^3=0
    dsimp [m] at m1 m2 m3
    unfold M at m1 m2 m3
    norm_num at m1 m2 m3
    linear_combination -7560*m1+3780*m2-420*m3
  · change -15*c^2*z^3+180*c^2*z^2-540*c^2*z+360*c^2-15*c*s*z^3+
      180*c*s*z^2-540*c*s*z+360*c*s-12*c*z^4+135*c*z^3-360*c*z^2+180*c*z-
      12*s*z^4+135*s*z^3-360*s*z^2+180*s*z-15*t*z^3+180*t*z^2-540*t*z+360*t-
      10*z^5+108*z^4-270*z^3+120*z^2=0
    unfold Q at q0
    norm_num at q0
    linear_combination -60*q0

end
end RKResearch.Certified.SDIRKSevenDirtyEarlyAliases
