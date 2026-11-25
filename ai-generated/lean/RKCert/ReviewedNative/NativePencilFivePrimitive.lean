module

public import RKCert.ReviewedNative.NativePencilPhysicalPorts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The original five cubic pencil ports, with arbitrary shared leakage

The polynomial may be any nonzero polynomial of degree at most three. It
is not assumed to equal a normalized mask. Only the actual two pencil
roots, the five literal primitive equations, and the nonzero complementary
pencil coefficient are used. In particular division by F(t) or j(t) is
never required to descend polynomial coprimality. -/
namespace RKResearch.Certified.Graded.NativePencilPorts
open Polynomial NativeLobatto
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def moment (P : K[X]) (n : ℕ) (x : K) : K := (primitive (X^n*P)).eval x

/-- Substitution by tX transports the zero-constant weighted primitive with
its exact homogeneous power of t. The statement also holds at t=0. -/
theorem moment_dilate (P : K[X]) (n : ℕ) (t x : K) :
    t^(n+1)*moment (P.comp (C t*X)) n x = moment P n (t*x) := by
  induction P using Polynomial.induction_on' with
  | add A B ha hb =>
    simpa only [moment,add_comp,mul_add,map_add,eval_add] using congrArg₂ (·+·) ha hb
  | monomial m a =>
    have comp : (monomial m a).comp (C t*X) = monomial m (a*t^m) := by
      rw [monomial_comp,mul_pow,← C_pow,← mul_assoc,← C_mul,C_mul_X_pow_eq_monomial]
    simp only [moment,comp,X_pow_mul_monomial,primitive_monomial,eval_monomial,
      mul_pow,pow_add,pow_one]
    ring

private def pol3 (a b c d : K) : K[X] :=
  monomial 0 a + monomial 1 b + monomial 2 c + monomial 3 d

private theorem pol3_rep (Q : K[X]) (hd : Q.natDegree≤3) :
    Q=pol3 (Q.coeff 0) (Q.coeff 1) (Q.coeff 2) (Q.coeff 3) := by
  classical
  have h : ofFn 4 (toFn 4 Q)=Q := ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hd)
  simpa [ofFn_eq_sum_monomial,Fin.sum_univ_succ,toFn,pol3,add_assoc] using h.symm

private def i1 (a b c d x : K) := a*x^2/2 + b*x^3/3 + c*x^4/4 + d*x^5/5
private def i2 (a b c d x : K) := a*x^3/3 + b*x^4/4 + c*x^5/5 + d*x^6/6
private def i3 (a b c d x : K) := a*x^4/4 + b*x^5/5 + c*x^6/6 + d*x^7/7

private theorem moment1 (a b c d x : K) : moment (pol3 a b c d) 1 x=i1 a b c d x := by
  simp only [moment,pol3,mul_add,X_pow_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,i1]
  norm_num <;> ring
private theorem moment2 (a b c d x : K) : moment (pol3 a b c d) 2 x=i2 a b c d x := by
  simp only [moment,pol3,mul_add,X_pow_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,i2]
  norm_num <;> ring
private theorem moment3 (a b c d x : K) : moment (pol3 a b c d) 3 x=i3 a b c d x := by
  simp only [moment,pol3,mul_add,X_pow_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,i3]
  norm_num <;> ring

private theorem mask_profile (Q : K[X]) (hd : Q.natDegree≤3) (nq : Q≠0) (z : K)
    (zn : z≠0) (z1 : z≠1) (p1 : moment Q 1 1=0) (p2 : moment Q 2 1=0)
    (mix : moment Q 2 z-moment Q 1 z=0) :
    ∃ g : K, g≠0 ∧ Q=C g*cubicMask z ∧
      420*moment Q 3 1= -g*cubicD z ∧ 420*(moment Q 3 z-moment Q 2 z)=g*z^4*cubicN z := by
  let a:=Q.coeff 0; let b:=Q.coeff 1; let c:=Q.coeff 2; let d:=Q.coeff 3
  have rep : Q=pol3 a b c d := pol3_rep Q hd
  rw [rep,moment1] at p1
  rw [rep,moment2] at p2
  rw [rep,moment2,moment1] at mix
  unfold i1 at p1 mix
  unfold i2 at p2 mix
  have ae : a=(3/10:K)*c+(2/5:K)*d := by linear_combination 18*p1-24*p2
  have be : b= -(6/5:K)*c-(6/5:K)*d := by linear_combination -24*p1+36*p2
  rw [ae,be] at mix
  let L : K := 3*(4*z-3)
  let M : K := 2*(5*z^2+4*z-6)
  let U : K := (20*z+31)/9
  let V : K := -8/3
  have unit : U*L+V*M=1 := by dsimp only [U,L,V,M]; ring
  have small : L*c+M*d=0 := by
    have f : (z^2*(z-1)^2)*(L*c+M*d)=0 := by
      dsimp only [L,M]
      linear_combination 60*mix
    exact (mul_eq_zero.mp f).resolve_left (mul_ne_zero (pow_ne_zero _ zn) (pow_ne_zero _ (sub_ne_zero.mpr z1)))
  let g := (U*d-V*c)/5
  have cg : c=g*(-5*M) := by dsimp only [g]; linear_combination U*small-c*unit
  have dg : d=g*(5*L) := by dsimp only [g]; linear_combination V*small-d*unit
  have ag : a=g*(12*z-15*z^2) := by rw [ae,cg,dg]; dsimp only [L,M]; ring
  have bg : b=g*(60*z^2-24*z-18) := by rw [be,cg,dg]; dsimp only [L,M]; ring
  have form : Q = C g*cubicMask z := by
    rw [rep,ag,bg,cg,dg]
    letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    simp only [pol3,cubicMask,L,M,eval_monomial,eval_C,eval_mul,eval_add,eval_sub,
      eval_pow,eval_X,eval_ofNat,pow_zero,pow_one,mul_one]
    ring
  have gn : g≠0 := by intro hg; exact nq (by simpa [hg] using form)
  refine ⟨g,gn,form,?_,?_⟩
  · rw [rep,moment3,ag,bg,cg,dg]
    dsimp only [i3,L,M,cubicD]
    ring
  · rw [rep,moment3,moment2,ag,bg,cg,dg]
    dsimp only [i3,i2,L,M,cubicN]
    ring

private theorem dilation_inverse (P : K[X]) (t : K) (tn:t≠0) :
    (P.comp (C t*X)).comp (C t⁻¹*X) = P := by
  rw [comp_assoc,mul_comp,C_comp,X_comp,← mul_assoc,← C_mul,mul_inv_cancel₀ tn,C_1,one_mul,comp_X]

/-- Five original primitive equations for an arbitrary profile, not a
presumed kernel vector. Amplitudes a,b are the pencil coefficients, k is
one literal shared leakage (zero is allowed). -/
theorem five_physical_ports_scaled_coprime (P : K[X]) (pd : P.natDegree≤3) (pn : P≠0)
    (a b k t z : K) (bn : b≠0) (tn : t≠0) (zn : z≠0) (z1 : z≠1)
    (rt : a*radauQuotient t+b*lobattoValue t=0)
    (ru : a*radauQuotient (t*z)+b*lobattoValue (t*z)=0)
    (h1 : moment P 1 t=0) (h2 : moment P 2 t=0)
    (h3 : moment P 3 t=k*radauValue t)
    (h4 : moment P 2 (t*z)-t*moment P 1 (t*z)=0)
    (h5 : moment P 3 (t*z)-t*moment P 2 (t*z)=k*radauValue (t*z)) :
    IsCoprime (pencilContrast t) (P.comp (C t*X)) := by
  let Q := P.comp (C t*X)
  have qd : Q.natDegree≤3 := by
    have bound : Q.natDegree ≤ P.natDegree * (C t*X).natDegree := natDegree_comp_le
    rw [natDegree_C_mul_X t tn,mul_one] at bound
    exact bound.trans pd
  have qn : Q≠0 := by
    intro e
    apply pn
    rw [← dilation_inverse P t tn]
    change Q.comp (C t⁻¹*X)=0
    rw [e,zero_comp]
  have h11 : t^2*moment Q 1 1=moment P 1 t := by simpa only [mul_one] using moment_dilate P 1 t 1
  have h21 : t^3*moment Q 2 1=moment P 2 t := by simpa only [mul_one] using moment_dilate P 2 t 1
  have h31 : t^4*moment Q 3 1=moment P 3 t := by simpa only [mul_one] using moment_dilate P 3 t 1
  have h1z : t^2*moment Q 1 z=moment P 1 (t*z) := moment_dilate P 1 t z
  have h2z : t^3*moment Q 2 z=moment P 2 (t*z) := moment_dilate P 2 t z
  have h3z : t^4*moment Q 3 z=moment P 3 (t*z) := moment_dilate P 3 t z
  have n1 := (mul_eq_zero.mp (h11.trans h1)).resolve_left (pow_ne_zero _ tn)
  have n2 := (mul_eq_zero.mp (h21.trans h2)).resolve_left (pow_ne_zero _ tn)
  have n12 : moment Q 2 z-moment Q 1 z=0 := by
    have zero : t^3*(moment Q 2 z-moment Q 1 z)=0 := by linear_combination h2z-t*h1z+h4
    exact (mul_eq_zero.mp zero).resolve_left (pow_ne_zero _ tn)
  obtain ⟨g,gn,form,high,mixed⟩ := mask_profile Q qd qn z zn z1 n1 n2 n12
  have l1 : t^4*moment Q 3 1=k*t*radauQuotient t := by rw [h31,h3,radauValue]; ring
  have l2 : t^4*(moment Q 3 z-moment Q 2 z)=k*(t*z)*radauQuotient (t*z) := by
    unfold radauValue at h5
    linear_combination h3z-t*h2z+h5
  have inv : radauQuotient t*(moment Q 3 z-moment Q 2 z) -
      z*radauQuotient (t*z)*moment Q 3 1=0 := by
    have e : t^4*(radauQuotient t*(moment Q 3 z-moment Q 2 z) -
        z*radauQuotient (t*z)*moment Q 3 1)=0 := by
      linear_combination (radauQuotient t)*l2-(z*radauQuotient (t*z))*l1
    exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ tn)
  have jgate : cubicD z*radauQuotient (t*z)+z^3*cubicN z*radauQuotient t=0 := by
    have e : (g*z)*(cubicD z*radauQuotient (t*z)+z^3*cubicN z*radauQuotient t)=0 := by
      linear_combination 420*inv + (z*radauQuotient (t*z))*high-(radauQuotient t)*mixed
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero gn zn)
  have fgate : cubicD z*lobattoValue (t*z)+z^3*cubicN z*lobattoValue t=0 := by
    have e : b*(cubicD z*lobattoValue (t*z)+z^3*cubicN z*lobattoValue t)=0 := by
      linear_combination (cubicD z)*ru + (z^3*cubicN z)*rt-a*jgate
    exact (mul_eq_zero.mp e).resolve_left bn
  change IsCoprime _ Q
  rw [form]
  exact (isCoprime_mul_unit_left_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr gn)) _ _).mpr
    (cubic_pencil_ports_coprime z t zn z1 tn fgate jgate)

/-- The full unscaled mesh divided by X. -/
def pencilQuotient (a b : K) : K[X] := C a*radauQuotient X+C b*lobattoValue X

private theorem comp_contrast (t:K) (tn:t≠0) :
    (pencilContrast t).comp (C t⁻¹*X) = C (lobattoValue t)*radauQuotient X-C (radauQuotient t)*lobattoValue X := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  have back : t*(t⁻¹*x)=x := by rw [← mul_assoc,mul_inv_cancel₀ tn,one_mul]
  simp only [eval_comp,pencilContrast,lobattoValue,radauQuotient,eval_mul,eval_add,
    eval_sub,eval_pow,eval_X,eval_C,eval_ofNat,eval_one,back]

/-- The genuine cubic profile is coprime to the full original pencil
quotient over K. No condition at either root is imposed on F(t) or j(t). -/
theorem five_physical_ports_coprime (P : K[X]) (pd : P.natDegree≤3) (pn : P≠0)
    (a b k t z : K) (bn : b≠0) (tn : t≠0) (zn : z≠0) (z1 : z≠1)
    (rt : a*radauQuotient t+b*lobattoValue t=0)
    (ru : a*radauQuotient (t*z)+b*lobattoValue (t*z)=0)
    (h1 : moment P 1 t=0) (h2 : moment P 2 t=0)
    (h3 : moment P 3 t=k*radauValue t)
    (h4 : moment P 2 (t*z)-t*moment P 1 (t*z)=0)
    (h5 : moment P 3 (t*z)-t*moment P 2 (t*z)=k*radauValue (t*z)) :
    IsCoprime (pencilQuotient a b) P := by
  have hc := (five_physical_ports_scaled_coprime P pd pn a b k t z bn tn zn z1 rt ru h1 h2 h3 h4 h5).map
    (compRingHom (C t⁻¹*X))
  change IsCoprime ((pencilContrast t).comp (C t⁻¹*X)) ((P.comp (C t*X)).comp (C t⁻¹*X)) at hc
  rw [comp_contrast t tn,dilation_inverse P t tn] at hc
  let d := -radauQuotient t/b
  have da : d*a=lobattoValue t := by dsimp only [d]; field_simp [bn]; linear_combination -rt
  have db : d*b= -radauQuotient t := by dsimp only [d]; exact div_mul_cancel₀ _ bn
  apply hc.of_isCoprime_of_dvd_left
  refine ⟨C d,?_⟩
  calc
    C (lobattoValue t)*radauQuotient X-C (radauQuotient t)*lobattoValue X =
        C (d*a)*radauQuotient X+C (d*b)*lobattoValue X := by
      simp only [da,db,map_neg,neg_mul,sub_eq_add_neg]
    _ = pencilQuotient a b*C d := by
      simp only [pencilQuotient,map_mul]
      ring

/-- The paid identity `(X W) T=Q P`, with `natDegree Q < natDegree W` and
an actual nonzero mesh numerator Q, is now incompatible with the five ports. -/
theorem no_low_degree_mesh_identity {W P Q T : K[X]} (hp : IsCoprime W P)
    (qn : Q≠0) (deg : Q.natDegree < W.natDegree) (mesh : (X*W)*T=Q*P) : False := by
  have d : W ∣ Q*P := ⟨X*T,by rw [← mesh]; ring⟩
  obtain ⟨S,hS⟩ := hp.dvd_of_dvd_mul_right d
  have wn : W≠0 := by intro h; simp [h] at deg
  have sn : S≠0 := by intro h; exact qn (by simpa [h] using hS)
  rw [hS,natDegree_mul wn sn] at deg
  omega

/-- A full, non-generic degree-six floor as soon as the j coefficient is nonzero. -/
theorem pencilQuotient_degree_floor (a b : K) (an : a≠0) : 6 ≤ (pencilQuotient a b).natDegree := by
  let l : List K := [7*a-b, -168*a+20*b, 1260*a-120*b, -4200*a+300*b,
    6930*a-330*b, -5544*a+132*b, 1716*a]
  have shape : pencilQuotient a b = NativePencilProjection.pack l := by
    letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    simp only [pencilQuotient,NativePencilProjection.pack,NativeHornerWitness.horner,
      l,lobattoValue,radauQuotient,eval_C,eval_X,eval_add,eval_sub,eval_mul,eval_pow,
      eval_ofNat,eval_one,eval_zero]
    ring
  apply le_natDegree_of_ne_zero
  rw [shape,NativePencilProjection.pack_coeff]
  change 1716*a ≠ 0
  exact mul_ne_zero (by norm_num) an

/-- The early low-profile contradiction on the actual five primitive probes
and scalar mesh identity: all numerators of degree at most five are covered. -/
theorem zero_of_five_physical_ports_and_mesh (P N T : K[X]) (pd : P.natDegree≤3)
    (nd : N.natDegree≤5) (nn : N≠0) (a b k t z : K) (an : a≠0) (bn : b≠0)
    (tn : t≠0) (zn : z≠0) (z1 : z≠1)
    (rt : a*radauQuotient t+b*lobattoValue t=0)
    (ru : a*radauQuotient (t*z)+b*lobattoValue (t*z)=0)
    (h1 : moment P 1 t=0) (h2 : moment P 2 t=0)
    (h3 : moment P 3 t=k*radauValue t)
    (h4 : moment P 2 (t*z)-t*moment P 1 (t*z)=0)
    (h5 : moment P 3 (t*z)-t*moment P 2 (t*z)=k*radauValue (t*z))
    (mesh : (X * pencilQuotient a b) * T=N*P) : P=0 := by
  by_contra pn
  have cop := five_physical_ports_coprime P pd pn a b k t z bn tn zn z1 rt ru h1 h2 h3 h4 h5
  have floor := pencilQuotient_degree_floor a b an
  exact no_low_degree_mesh_identity cop nn (by omega) mesh

/-- Small integral Bezout identity for the original primal polynomials. This
can be used instead of a modular coprimality check at a single knot. -/
theorem no_common_lobatto_radau_quotient (t : K) (ft : lobattoValue t=0) : radauQuotient t ≠ 0 := by
  intro jt
  have e : (60060*t^5-164010*t^4+163548*t^3-71925*t^2+13137*t-705)*lobattoValue t+
      (-4620*t^4+9240*t^3-6111*t^2+1491*t-100)*radauQuotient t=5 := by
    unfold lobattoValue radauQuotient
    ring
  simp only [ft,jt,mul_zero,add_zero] at e
  norm_num at e

end
end RKResearch.Certified.Graded.NativePencilPorts
