module

public import RKCert.ReviewedNative.NativeQuadraticClassSelector
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Count all physical pairs on a quadratic mesh, including common roots

This is the upper-bound direction before the pair count is known. A clock
occurring twice contributes a double factor; this remains true for Q=0. -/
namespace RKResearch.Certified.Graded.NativeQuadraticClassSelector

open Polynomial
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
variable {G Q R P : K[X]}

private theorem pair_snd_ne {S : Finset (K×K)} {a : K} {p q : K×K}
    (hp : p∈clockFiber S a) (hq : q∈clockFiber S a) (ne : p≠q) : p.2≠q.2 :=
  fun same => ne (Prod.ext ((mem_clockFiber.mp hp).2.symm.trans (mem_clockFiber.mp hq).2) same)

private theorem pair_mesh_at {S : Finset (K×K)} {a : K} {p : K×K}
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2) (hp : p∈clockFiber S a) :
    G.eval a=Q.eval a*p.2 := by
  obtain ⟨h,e⟩ := mem_clockFiber.mp hp
  simpa only [←e] using mesh p h

private theorem pair_mesh_zero_of_two {S : Finset (K×K)} {a : K} {p q : K×K}
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (hp : p∈clockFiber S a) (hq : q∈clockFiber S a) (ne : p≠q) :
    G.eval a=0 ∧ Q.eval a=0 := by
  have e₁ := pair_mesh_at mesh hp
  have e₂ := pair_mesh_at mesh hq
  have eq : (p.2-q.2)*Q.eval a=0 := by
    linear_combination e₂ - e₁
  have q0 := (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr (pair_snd_ne hp hq ne))
  exact ⟨by rw [e₁,q0,zero_mul],q0⟩

private theorem pair_eliminant_zero {a z : K}
    (mesh : G.eval a=Q.eval a*z) (square : z^2=R.eval a*z+P.eval a) :
    (eliminant G Q R P).eval a=0 := by
  simp only [eliminant,eval_sub,eval_mul,eval_pow,mesh]
  linear_combination (Q.eval a)^2 * square

private theorem pair_eliminant_factor {a : K} {g q : K[X]}
    (hg : G=(X-C a)*g) (hq : Q=(X-C a)*q) :
    eliminant G Q R P=(X-C a)^2*eliminant g q R P := by
  simp only [eliminant,hg,hq]
  ring

private theorem pair_square_dvd_eliminant {a : K}
    (g0 : G.eval a=0) (q0 : Q.eval a=0) :
    (X-C a)^2∣eliminant G Q R P := by
  obtain ⟨g,hg⟩ := (dvd_iff_isRoot (a:=a)).mpr g0
  obtain ⟨q,hq⟩ := (dvd_iff_isRoot (a:=a)).mpr q0
  exact ⟨eliminant g q R P,pair_eliminant_factor hg hq⟩

private theorem pair_eliminant_factors (S : Finset (K×K))
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1) (a : K) :
    (X-C a)^(clockFiber S a).card∣eliminant G Q R P := by
  have cap := clockFiber_card_le_two S square a
  by_cases e₀ : (clockFiber S a).card=0
  · rw [e₀,pow_zero]
    exact one_dvd _
  by_cases e₁ : (clockFiber S a).card=1
  · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(clockFiber S a).card)
    obtain ⟨h,e⟩ := mem_clockFiber.mp hp
    have wp : p.2^2=R.eval a*p.2+P.eval a := by simpa only [←e] using square p h
    rw [e₁,pow_one]
    exact dvd_iff_isRoot.mpr (pair_eliminant_zero (pair_mesh_at mesh hp) wp)
  have e₂ : (clockFiber S a).card=2 := by omega
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (by omega : 1<(clockFiber S a).card)
  obtain ⟨g0,q0⟩ := pair_mesh_zero_of_two mesh hp hq ne
  rw [e₂]
  exact pair_square_dvd_eliminant g0 q0

/-- Distinct physical pairs are counted with their clock multiplicities. -/
theorem pair_count_le_eliminant_degree (S : Finset (K×K))
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (nz : eliminant G Q R P ≠ 0) : S.card ≤ (eliminant G Q R P).natDegree := by
  have prod := counted_clock_product_dvd S nz (pair_eliminant_factors S mesh square)
  have cover : S.val.map Prod.fst ≤ (eliminant G Q R P).roots := by
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots nz (S.val.map Prod.fst)).mp
    simpa only [Multiset.map_map,Function.comp_def] using prod
  have bound := (Multiset.card_le_card cover).trans (card_roots' _)
  simpa only [Multiset.card_map,Finset.card_val] using bound

theorem leading_pair_count_le_fourteen (S : Finset (K×K))
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (gd : G.natDegree=7) (qd : Q.natDegree≤3) (rd : R.natDegree≤4) (pd : P.natDegree≤6)
    (top : (G-R*Q).coeff 7≠0) : S.card ≤ 14 := by
  have deg := eliminant_degree_fourteen gd qd rd pd top
  have nz : eliminant G Q R P ≠ 0 := by
    intro z
    rw [z,natDegree_zero] at deg
    omega
  exact (pair_count_le_eliminant_degree S mesh square nz).trans deg.le

end
end RKResearch.Certified.Graded.NativeQuadraticClassSelector
