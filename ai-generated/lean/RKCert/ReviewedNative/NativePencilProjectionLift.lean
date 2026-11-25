module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Uniform common-root obstructions from two fixed-size projections

This scalar algebra is independent of tableau hypotheses. There is no claim
that arbitrary characteristic-zero coefficients have a prime residue map.
Only the two *integer* projection polynomials are reduced. A nonzero fixed
Sylvester determinant supplies an ordinary Bezout identity even on a fiber
where the degree of either input falls. -/

namespace RKResearch.Certified.Graded.NativePencilProjection

open Polynomial

noncomputable section

/-- At positive total size, a common zero kills the fixed-size determinant,
even when both polynomials lose degree on this particular fiber. -/
theorem fixed_resultant_zero_of_common_root {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (f g : R[X]) (m n : ℕ) (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (pos : m ≠ 0 ∨ n ≠ 0) (a : K)
    (fz : f.eval₂ φ a = 0) (gz : g.eval₂ φ a = 0) :
    φ (f.resultant g m n) = 0 := by
  obtain ⟨u,v,_,_,h⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg pos
  have e := congrArg (fun h : R[X] => h.eval₂ φ a) h
  simpa only [eval₂_add, eval₂_mul, fz, gz, zero_mul, add_zero, eval₂_C] using e.symm

/-- A nonvanishing fixed-size determinant proves coprimality over the fiber
field, not merely that the two polynomials have no root in that field. -/
theorem coprime_of_fixed_resultant_ne_zero {K : Type*} [Field K]
    (f g : K[X]) (m n : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (pos : m ≠ 0 ∨ n ≠ 0) (hn : f.resultant g m n ≠ 0) : IsCoprime f g := by
  obtain ⟨u,v,_,_,h⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg pos
  let c := (f.resultant g m n)⁻¹
  refine ⟨C c * u, C c * v, ?_⟩
  calc
    C c * u * f + C c * v * g = C c * (f*u+g*v) := by ring
    _ = 1 := by rw [h, ← C_mul, show c * f.resultant g m n = 1 from inv_mul_cancel₀ hn, C_1]

/-- If the first input keeps its leading coefficient on reduction, a modular
Bezout test lifts to every injective characteristic-zero coefficient model.
The second input is explicitly allowed to lose degree modulo the prime. -/
theorem coprime_of_residue {R K k : Type*} [CommRing R] [Field K] [Field k]
    (i : R →+* K) (inj : Function.Injective i) (q : R →+* k)
    (f g : R[X]) (lc : q f.leadingCoeff ≠ 0)
    (hc : IsCoprime (f.map q) (g.map q)) : IsCoprime (f.map i) (g.map i) := by
  let F := f.map q
  let G := g.map q
  have fm : F.natDegree = f.natDegree := natDegree_map_of_leadingCoeff_ne_zero q lc
  have gn : G.natDegree ≤ g.natDegree := natDegree_map_le
  have fc : F.coeff F.natDegree ≠ 0 := by
    rw [fm, show F.coeff f.natDegree = q f.leadingCoeff from by
      simp only [F,coeff_map,coeff_natDegree]]
    exact lc
  have pad : F.resultant G f.natDegree g.natDegree =
      F.coeff F.natDegree ^ (g.natDegree-G.natDegree) * F.resultant G := by
    calc
      F.resultant G f.natDegree g.natDegree =
          F.resultant G F.natDegree (G.natDegree + (g.natDegree-G.natDegree)) := by
            rw [fm, Nat.add_sub_of_le gn]
      _ = _ := resultant_add_right_deg F G F.natDegree G.natDegree _ le_rfl
  have hmod : F.resultant G f.natDegree g.natDegree ≠ 0 := by
    rw [pad]
    exact mul_ne_zero (pow_ne_zero _ fc) (resultant_ne_zero F G hc)
  have base : f.resultant g ≠ 0 := by
    intro h
    apply hmod
    change (f.map q).resultant (g.map q) f.natDegree g.natDegree = 0
    rw [resultant_map_map, h, map_zero]
  have hf : (f.map i).natDegree = f.natDegree := natDegree_map_eq_of_injective inj f
  have hg : (g.map i).natDegree = g.natDegree := natDegree_map_eq_of_injective inj g
  by_contra bad
  have fn : f.map i ≠ 0 := by
    intro hz
    have hmap : f.map i = (0 : R[X]).map i := by rw [Polynomial.map_zero]; exact hz
    have ef : f = 0 := Polynomial.map_injective i inj hmap
    exact lc (by simp [ef])
  have e := (resultant_eq_zero_iff (f:=f.map i) (g:=g.map i)).mpr ⟨Or.inl fn,bad⟩
  rw [hf,hg,resultant_map_map] at e
  exact base (inj (e.trans i.map_zero.symm))

/-- Integer z-polynomials; polynomials in t with those coefficients; then in x. -/
abbrev ZPoly := Polynomial ℤ
abbrev TPoly := Polynomial ZPoly
abbrev XPoly := Polynomial TPoly

abbrev zEval {K : Type*} [Field K] (z : K) : ZPoly →+* K :=
  eval₂RingHom (Int.castRingHom K) z

abbrev tEval {K : Type*} [Field K] (z t : K) : TPoly →+* K :=
  eval₂RingHom (zEval z) t

/-- Remove only a known integer content and known origin power. No division
by the leading coefficient of a first subresultant is needed. -/
theorem primitive_projection_root {K : Type*} [Field K] [CharZero K]
    (A B : TPoly) (m n : ℕ) (am : A.natDegree ≤ m) (bn : B.natDegree ≤ n)
    (pos : m ≠ 0 ∨ n ≠ 0) (r : ZPoly) (d : ℤ) (e : ℕ) (dn : d ≠ 0)
    (id : A.resultant B m n = C d * X^e * r)
    (z t : K) (zn : z ≠ 0) (az : tEval z t A = 0) (bz : tEval z t B = 0) :
    zEval z r = 0 := by
  have h := fixed_resultant_zero_of_common_root (zEval z) A B m n am bn pos t az bz
  rw [id,map_mul,map_mul,map_pow] at h
  have hd : zEval z (C d) = (d:K) := eval₂_C _ _
  have hx : zEval z X = z := eval₂_X _ _
  rw [hd,hx] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (Int.cast_ne_zero.mpr dn) (pow_ne_zero _ zn))

/-- On a root of r and a genuine t-root of A, the second projection B
cannot vanish if its fixed resultant with A is a unit modulo (p,r). -/
theorem projected_value_ne_zero {K k : Type*} [Field K] [CharZero K] [Field k]
    (q : ℤ →+* k) (r : ZPoly) (lc : q r.leadingCoeff ≠ 0) (A B : TPoly)
    (m n : ℕ) (am : A.natDegree ≤ m) (bn : B.natDegree ≤ n) (pos : m ≠ 0 ∨ n ≠ 0)
    (hc : IsCoprime (r.map q) ((A.resultant B m n).map q))
    (z t : K) (rz : zEval z r = 0) (az : tEval z t A = 0) : tEval z t B ≠ 0 := by
  intro bz
  have bad := fixed_resultant_zero_of_common_root (zEval z) A B m n am bn pos t az bz
  let i := Int.castRingHom K
  have hi : Function.Injective i := Int.cast_injective
  obtain ⟨u,v,huv⟩ := coprime_of_residue i hi q r (A.resultant B m n) lc hc
  have e := congrArg (fun p : K[X] => p.eval z) huv
  have r0 : (r.map i).eval z = 0 := by rw [eval_map]; exact rz
  have b0 : ((A.resultant B m n).map i).eval z = 0 := by rw [eval_map]; exact bad
  simpa only [eval_add,eval_mul,r0,b0,mul_zero,add_zero,eval_one,zero_ne_one] using e

/-- Nested version. A uniform result in K[X], even for nonalgebraically
closed K. Its only nonstructural premise is the univariate modular Bezout
certificate for r and the outer fixed resultant. -/
theorem projected_coprime {K k : Type*} [Field K] [CharZero K] [Field k]
    (q : ℤ →+* k) (r : ZPoly) (lc : q r.leadingCoeff ≠ 0)
    (A : TPoly) (H P : XPoly) (u v : ℕ) (hu : H.natDegree ≤ u) (pv : P.natDegree ≤ v)
    (uv : u ≠ 0 ∨ v ≠ 0) (m n : ℕ) (am : A.natDegree ≤ m)
    (qn : (H.resultant P u v).natDegree ≤ n) (mn : m ≠ 0 ∨ n ≠ 0)
    (hc : IsCoprime (r.map q) ((A.resultant (H.resultant P u v) m n).map q))
    (z t : K) (rz : zEval z r = 0) (az : tEval z t A = 0) :
    IsCoprime (H.map (tEval z t)) (P.map (tEval z t)) := by
  have hn := projected_value_ne_zero q r lc A (H.resultant P u v) m n am qn mn hc z t rz az
  apply coprime_of_fixed_resultant_ne_zero _ _ u v
    (natDegree_map_le.trans hu) (natDegree_map_le.trans pv) uv
  rw [resultant_map_map]
  exact hn

end
end RKResearch.Certified.Graded.NativePencilProjection
