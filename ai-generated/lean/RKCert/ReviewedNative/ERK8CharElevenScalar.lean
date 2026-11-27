module
public import RKCert.ReviewedNative.ERK8PaidLobatto
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-cleared scalar endpoints for the exceptional ERK8 characteristic

All identities hold over arbitrary extensions, not just the prime field.
The hypotheses are the extracted scalar equations, not literal tableau
order. The paid physical and Newton bridges are separate statements. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

variable {K : Type*} [Field K]

private theorem two_nz (p : (11:K)=0) : (2:K)≠0 := by
  intro z
  exact one_ne_zero (by linear_combination p-5*z : (1:K)=0)

private theorem three_nz (p : (11:K)=0) : (3:K)≠0 := by
  intro z
  exact one_ne_zero (by linear_combination 4*z-p : (1:K)=0)

private theorem seven_nz (p : (11:K)=0) : (7:K)≠0 := by
  intro z
  exact one_ne_zero (by linear_combination 8*z-5*p : (1:K)=0)

theorem omitted_root_eq_six (p : (11:K)=0) {u : K}
    (r : 14*u^3-21*u^2+9*u-1=0) (s : 91*u^2-105*u+27=0) : u=6 := by
  have f : (u-6)*(3*u+1)=0 := by
    linear_combination s-(8*u^2-8*u+3)*p
  rcases mul_eq_zero.mp f with h|h
  · exact sub_eq_zero.mp h
  · have e : u-7=0 := by linear_combination 4*h-(u+1)*p
    rw [sub_eq_zero.mp e] at r
    exact (seven_nz p (by linear_combination r-348*p : (7:K)=0)).elim

/-- The three off rows before the fourth at -1 cannot have the
required third-row primitive coefficients and quadratic remainder. -/
theorem impossible_first_clean_five_prefix (p : (11:K)=0) {a b d : K}
    (ad : d ≠ -1) (qa : a^2-a+8≠0)
    (E : 3*a*b+8*(a+b)+1=0)
    (F : -5+10*(a+b)-2*a*b+d*(10-a*b-2*(a+b))=0) : False := by
  have m : a*b-(a+b)-7=0 := by linear_combination 4*E-(a*b+3*(a+b)+1)*p
  have q : 3*((1-(a+b))*(1+d))=0 := by
    linear_combination F+(2+d)*m-((a+b)-2)*p
  have e : (1-(a+b))*(1+d)=0 := (mul_eq_zero.mp q).resolve_left (three_nz p)
  have ne : 1+d≠0 := by
    intro h
    apply ad
    linear_combination h
  have ab : 1-(a+b)=0 := (mul_eq_zero.mp e).resolve_right ne
  apply qa
  linear_combination -a*ab-m+ab

private theorem quadratics {x z : K} (s : x+z=1) (m : x*z=8) :
    x^2-x+8=0 ∧ z^2-z+8=0 := by
  exact ⟨by linear_combination x*s-m,by linear_combination z*s-m⟩

private theorem upper_products (p : (11:K)=0) {x z : K}
    (s : x+z=1) (m : x*z=8) :
    (6+2*x)*z^2=7 ∧ (6+2*z)*x^2=7 ∧
      (6+2*x)*z=5*x ∧ (6+2*z)*x=5*z := by
  obtain ⟨hx,hz⟩ := quadratics s m
  exact ⟨by linear_combination (6+2*x)*hz+6*s+2*m-(3+2*x)*p,
    by linear_combination (6+2*z)*hx+6*s+2*m-(3+2*z)*p,
    by linear_combination 6*s+2*m+(2-x)*p,
    by linear_combination 6*s+2*m+(2-z)*p⟩

/-- Four-off late reverse ratio (and the five-off staggered tail) reject
the actual first four off-clock remainder 6+2X. -/
theorem impossible_four_late (p : (11:K)=0) {x z : K}
    (s : x+z=1) (m : x*z=8)
    (H : (6+2*z)*x^3+(6+2*x)*z^2*(3*x-2*z)=0) : False := by
  obtain ⟨U,V,_,_⟩ := upper_products p s m
  have q : (2:K)*7*(2*x-z)=0 := by
    linear_combination H-x*V-(3*x-2*z)*U
  have zq := (mul_eq_zero.mp q).resolve_left (mul_ne_zero (two_nz p) (seven_nz p))
  have xu : x-4=0 := by linear_combination 4*(s+zq)-x*p
  have qx := (quadratics s m).1
  rw [sub_eq_zero.mp xu] at qx
  exact one_ne_zero (by linear_combination 5*qx-9*p : (1:K)=0)

/-- With both quadratic clean roots terminal in the seven-clock list,
the fifth off clock is forced to repeat 2. -/
theorem fifth_off_eq_two (p : (11:K)=0) {x z e : K}
    (s : x+z=1) (m : x*z=8)
    (H :
      3*((6+2*x)*z^2*(x-e)+(6+2*z)*x^2*(z-e))*
        ((6+2*x)*z^2+(6+2*z)*x^2)
      -2*((6+2*x)*z*(x-e)+(6+2*z)*x*(z-e))*
        (((6+2*x)*z^2)*z+((6+2*z)*x^2)*x)=0) : e=2 := by
  obtain ⟨U,V,W,Z⟩ := upper_products p s m
  rw [U,V,W,Z] at H
  have a : 7*(x-e)+7*(z-e)=7*(1-2*e) := by linear_combination 7*s
  have b : 7*z+7*x=7 := by linear_combination 7*s
  have c : x^2+z^2=7 := by linear_combination (x+z+1)*s-2*m-2*p
  have d : 5*x*(x-e)+5*z*(z-e)=5*(7-e) := by linear_combination 5*c-5*e*s
  rw [a,b,d] at H
  apply sub_eq_zero.mp
  linear_combination -H-(18+47*e)*p

/-- The high-off tail reverse consistency forces the product 8. -/
theorem high_tail_product (p : (11:K)=0) {u v : K} (ne : u≠v)
    (qu : u^2-u+8≠0) (qv : v^2-v+8≠0)
    (eq : (3*(1-u)^2-(1-u))/(u^2-u+8) =
       (3*(1-v)^2-(1-v))/(v^2-v+8)) : u*v=8 := by
  have cross := (div_eq_div_iff qu qv).mp eq
  have cleared : (u-v)*(2*(u*v-8))=0 := by
    linear_combination cross-2*(u-v)*(u+v-1)*p
  exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp cleared).resolve_left
    (sub_ne_zero.mpr ne))).resolve_left (two_nz p))

/-- The high-off three-node hull transfer then forces the fifth off
clock to repeat the fourth. Its remainder comparison uses no root
splitting hypothesis. -/
theorem high_fifth_eq_two (p : (11:K)=0) {u v f c : K}
    (qu : u^2-u+8≠0) (product : u*v=8)
    (a : -8*(1-(u+v))=c) (d : (1-(u+v))*(1-f)=7*c) : f=2 := by
  have nz : (1-(u+v))≠0 := by
    intro e
    exact qu (by linear_combination -u*e-product)
  have e : (1-(u+v))*(2-f)=0 := by
    linear_combination d-7*a-5*(1-(u+v))*p
  exact (sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left nz)).symm

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.omitted_root_eq_six
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.impossible_first_clean_five_prefix
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.impossible_four_late
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.fifth_off_eq_two
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.high_tail_product
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.high_fifth_eq_two
