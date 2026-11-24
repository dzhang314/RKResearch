module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section
/-! # A single two-site recurrence for the reverse rank-one obstruction
The cancellation works for arbitrary distinct nonzero t,u, including when
either equals the localized quadratic site. No determinant or split cases
for degenerate minors are used.
-/
namespace RKCert.ReverseTwoNode
variable {K : Type*} [Field K] [CharZero K]

def gain (t x : K) : K := x*(2*x-3*t)/(4*t)
def slope (t u : K) : K := t/(3*t-2*u)

theorem gain_first {t : K} (ht:t≠0) : gain t t= -t/4 := by
  unfold gain; field_simp; ring

theorem head_first {t h g b q l k e : K}
    (ht:t≠0) (hh:h≠0) (h1:0=t*h/2+2*g)
    (h2:0=t^2*h/3+b*g) (h3:0=t^3*h/4+(q+l*t)*g)
    (h4:0=(k+e*t)*g) :
    g=gain t t*h ∧ g≠0 ∧ b=4*t/3 ∧ q+l*t=t^2 ∧ k+e*t=0 := by
  have g' : g= -t*h/4 := by linear_combination -h1/2
  have gn : g≠0 := by rw [g']; exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ht) hh) (by norm_num)
  refine ⟨by rw [gain_first ht,g']; ring,gn,?_,?_,(mul_eq_zero.mp h4.symm).resolve_right gn⟩
  · apply mul_right_cancel₀ gn
    calc b*g = -(t^2*h/3) := by linear_combination -h2
         _ = (4*t/3)*g := by rw [g']; ring
  · apply mul_right_cancel₀ gn
    calc (q+l*t)*g = -(t^3*h/4) := by linear_combination -h3
         _ = t^2*g := by rw [g']; ring

/-- Before the second h-node, all prior h inputs are from t. This identity
also applies at zero-weight rows and at the first second-node row. -/
theorem previous_gain {t x h g : K} (ht:t≠0)
    (he:t*(x*h/2+2*g)=x^2*h/3+(4*t/3)*g) : g=gain t x*h := by
  unfold gain
  linear_combination (norm := (field_simp [ht]; ring)) (3/(2*t))*he

theorem head_second {t u h g q l k e : K}
    (ht:t≠0) (hu:u≠0) (htu:u≠t) (hh:h≠0) (hg:g=gain t u*h)
    (hc:q+l*t=t^2) (hz:k+e*t=0)
    (h3:t^2*(u*h/2+2*g)=u^3*h/4+(q+l*u)*g)
    (h4:gain t t*(u*h/2+2*g)=(k+e*u)*g) :
    3*t-2*u≠0 ∧ g≠0 ∧ e=slope t u ∧ l=slope t u*(u-t) := by
  have v : (k+e*u)*g= -u*(u-t)*h/4 := by
    rw [←h4,hg,gain_first ht,gain]
    field_simp [ht]; ring
  have gn : g≠0 := by
    intro z; rw [z,mul_zero] at v
    exact (div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hu) (sub_ne_zero.mpr htu)) hh)
      (by norm_num : (4:K)≠0)) v.symm
  have den : 3*t-2*u≠0 := by
    intro z
    have z' : 2*u-3*t=0 := by linear_combination -z
    exact gn (by rw [hg,gain,z']; simp)
  have den₁ : t*3-u*2≠0 := by intro w; apply den; linear_combination w
  have den₂ : -(u*2)+t*3≠0 := by intro w; apply den; linear_combination w
  have hn : (u-t)*g≠0 := mul_ne_zero (sub_ne_zero.mpr htu) gn
  refine ⟨den,gn,?_,?_⟩
  · apply mul_right_cancel₀ hn
    have k' : k= -e*t := by linear_combination hz
    rw [k'] at v
    calc e*((u-t)*g)= -u*(u-t)*h/4 := by linear_combination v
         _ = slope t u*((u-t)*g) := by rw [hg,gain,slope]; ring_nf; field_simp [ht,den,den₁,den₂]; ring
  · apply mul_right_cancel₀ hn
    have q' : q=t^2-l*t := by linear_combination hc
    rw [q'] at h3
    calc l*((u-t)*g) = t^2*(u*h/2+2*g)-u^3*h/4-t^2*g := by linear_combination -h3
         _ = slope t u*(u-t)*((u-t)*g) := by rw [hg,gain,slope]; ring_nf; field_simp [ht,den,den₁,den₂]; ring

/-- T,S are the incoming masses of h from the two earlier node fibers.
A subtraction cancels h identically, giving (x-u)S=0. At a repeat x=u
the shifted head equation yields S=0 as well. -/
theorem two_node_step {t u x h g T S : K}
    (ht:t≠0) (hu:u≠0) (htu:u≠t) (hd:3*t-2*u≠0)
    (h1:T+S=x*h/2+2*g)
    (h2:t*T+u*S=x^2*h/3+(4*t/3)*g)
    (h3:t^2*T+u^2*S=x^3*h/4+(t^2+slope t u*(u-t)*(x-t))*g)
    (h4:gain t t*T+gain t u*S=slope t u*(x-t)*g)
    (h5:x=u → (u-t)*gain t u*S=0) :
    g=gain t x*h ∧ x*(x-t)*(x-u)*h=0 := by
  have hd₁ : t*3-u*2≠0 := by intro w; apply hd; linear_combination w
  have hd₂ : -(u*2)+t*3≠0 := by intro w; apply hd; linear_combination w
  have T' : T=x*h/2+2*g-S := by linear_combination h1
  have g' : g=gain t x*h-3*(u-t)*S/(2*t) := by
    unfold gain
    linear_combination (norm := (field_simp [ht]; ring)) (3/(2*t))*h2-(3/2)*h1
  rw [T',g'] at h3 h4
  have elim : (3/4:K)*(t-u)*(x-u)*S=0 := by
    unfold gain slope at h3 h4
    linear_combination (norm := (ring_nf; field_simp [ht,hd,hd₁,hd₂]; ring)) h3-(t/2)*h4
  have hn : gain t u≠0 := by
    apply div_ne_zero (mul_ne_zero hu _) (mul_ne_zero (by norm_num) ht)
    exact neg_ne_zero.mp (by simpa only [neg_sub] using hd)
  have s0 : S=0 := by
    by_cases hx : x=u
    · exact (mul_eq_zero.mp (h5 hx)).resolve_left (mul_ne_zero (sub_ne_zero.mpr htu) hn)
    · exact (mul_eq_zero.mp elim).resolve_left
        (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr htu.symm)) (sub_ne_zero.mpr hx))
  rw [s0] at g' h4
  refine ⟨by simpa using g',?_⟩
  unfold gain slope at h4
  linear_combination (norm := (ring_nf; field_simp [ht,hd,hd₁,hd₂]; ring)) (-2*(3*t-2*u))*h4

end RKCert.ReverseTwoNode
