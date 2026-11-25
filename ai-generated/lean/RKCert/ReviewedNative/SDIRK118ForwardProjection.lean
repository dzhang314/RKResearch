module

public import RKCert.ReviewedNative.SDIRK118InstantiationAdapters

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.ForwardChart

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation (coordinate)
open scoped Matrix FiniteRootedTree

variable {K : Type*} [Field K]

abbrev V (K : Type*) := Fin 4 → K
abbrev Quad (K : Type*) := K × K × K

def ev (x : K) : Quad K →ₗ[K] K where
  toFun q := q.1 + q.2.1*x + q.2.2*x^2
  map_add' p q := by
    change (p.1+q.1) + (p.2.1+q.2.1)*x + (p.2.2+q.2.2)*x^2 =
      (p.1+p.2.1*x+p.2.2*x^2) + (q.1+q.2.1*x+q.2.2*x^2)
    ring
  map_smul' k q := by
    change k*q.1 + (k*q.2.1)*x + (k*q.2.2)*x^2 =
      k*(q.1+q.2.1*x+q.2.2*x^2)
    ring

theorem ev_apply (x : K) (q : Quad K) :
    ev x q = q.1 + q.2.1*x + q.2.2*x^2 := rfl

/-- Unisolvence on the original three distinct forward clocks. -/
theorem quad_eq_of_three {x y z : K} {p q : Quad K}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ex : ev x p = ev x q) (ey : ev y p = ev y q) (ez : ev z p = ev z q) : p = q := by
  let a := p.1 - q.1
  let b := p.2.1 - q.2.1
  let c := p.2.2 - q.2.2
  simp only [ev_apply] at ex ey ez
  have f (u : K) (h : p.1+p.2.1*u+p.2.2*u^2 = q.1+q.2.1*u+q.2.2*u^2) :
      a+b*u+c*u^2=0 := by
    dsimp [a,b,c]
    linear_combination h
  have pxy : (x-y)*(b+c*(x+y))=0 := by linear_combination (f x ex) - (f y ey)
  have pxz : (x-z)*(b+c*(x+z))=0 := by linear_combination (f x ex) - (f z ez)
  have lxy := (mul_eq_zero.mp pxy).resolve_left (sub_ne_zero.mpr hxy)
  have lxz := (mul_eq_zero.mp pxz).resolve_left (sub_ne_zero.mpr hxz)
  have cyz : c*(y-z)=0 := by linear_combination lxy - lxz
  have hc : c=0 := (mul_eq_zero.mp cyz).resolve_right (sub_ne_zero.mpr hyz)
  have hb : b=0 := by simpa only [hc,zero_mul,add_zero] using lxy
  have ha : a=0 := by simpa only [hb,hc,zero_mul,add_zero] using f x ex
  exact Prod.ext (sub_eq_zero.mp ha)
    (Prod.ext (sub_eq_zero.mp hb) (sub_eq_zero.mp hc))

def ell (u v w : K) : Quad K :=
  (v*w/((u-v)*(u-w)), -(v+w)/((u-v)*(u-w)), ((u-v)*(u-w))⁻¹)

theorem ev_ell (u v w x : K) :
    ev x (ell u v w) = ((x-v)*(x-w))/((u-v)*(u-w)) := by
  simp only [ev_apply,ell,div_eq_mul_inv]
  ring

theorem ev_ell_here {u v w : K} (hv : u ≠ v) (hw : u ≠ w) :
    ev u (ell u v w) = 1 := by
  rw [ev_ell, div_self (mul_ne_zero (sub_ne_zero.mpr hv) (sub_ne_zero.mpr hw))]

theorem ev_ell_left (u v w : K) : ev v (ell u v w) = 0 := by
  simp only [ev_ell,sub_self,zero_mul,zero_div]

theorem ev_ell_right (u v w : K) : ev w (ell u v w) = 0 := by
  simp only [ev_ell,sub_self,mul_zero,zero_div]

def interp (c : V K) : V K →ₗ[K] Quad K where
  toFun v :=
    v 0 • ell (c 0) (c 1) (c 2) +
    v 1 • ell (c 1) (c 0) (c 2) +
    v 2 • ell (c 2) (c 0) (c 1)
  map_add' v w := by
    simp only [Pi.add_apply,add_smul]
    abel
  map_smul' k v := by
    simp only [Pi.smul_apply,smul_eq_mul,smul_add,mul_smul,RingHom.id_apply]

theorem interp_apply (c v : V K) :
    interp c v =
      v 0 • ell (c 0) (c 1) (c 2) +
      v 1 • ell (c 1) (c 0) (c 2) +
      v 2 • ell (c 2) (c 0) (c 1) := rfl

theorem interp_old (c v : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2) :
    ev (c 0) (interp c v) = v 0 ∧ ev (c 1) (interp c v) = v 1 ∧
    ev (c 2) (interp c v) = v 2 := by
  refine ⟨?_,?_,?_⟩
  · simp only [interp_apply,map_add,map_smul,ev_ell_here h01 h02,
      ev_ell_left,ev_ell_right,smul_eq_mul,mul_one,mul_zero,add_zero,zero_add]
  · simp only [interp_apply,map_add,map_smul,ev_ell_here h01.symm h12,
      ev_ell_left,ev_ell_right,smul_eq_mul,mul_one,mul_zero,add_zero,zero_add]
  · simp only [interp_apply,map_add,map_smul,ev_ell_here h02.symm h12.symm,
      ev_ell_left,ev_ell_right,smul_eq_mul,mul_one,mul_zero,add_zero,zero_add]

def sample (c : V K) : Quad K →ₗ[K] V K where
  toFun q i := ev (c i) q
  map_add' p q := by
    funext i
    exact map_add (ev (c i)) p q
  map_smul' k q := by
    funext i
    exact map_smul (ev (c i)) k q

theorem sample_apply (c : V K) (q : Quad K) (i : Fin 4) :
    sample c q i = ev (c i) q := rfl

theorem interp_sample (c : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2) (q : Quad K) :
    interp c (sample c q) = q := by
  obtain ⟨e0,e1,e2⟩ := interp_old c (sample c q) h01 h02 h12
  exact quad_eq_of_three h01 h02 h12 e0 e1 e2

def pivot (c g : V K) : K := g 3 - ev (c 3) (interp c g)

def defectCoef (c g : V K) : V K →ₗ[K] K :=
  (pivot c g)⁻¹ • (coordinate 3 - (ev (c 3)).comp (interp c))

theorem defectCoef_apply (c g v : V K) :
    defectCoef c g v = (v 3 - ev (c 3) (interp c v))/(pivot c g) := by
  change (pivot c g)⁻¹ * (v 3 - ev (c 3) (interp c v)) = _
  rw [div_eq_mul_inv]
  exact mul_comm _ _

def along (f : V K →ₗ[K] K) (q : Quad K) : V K →ₗ[K] Quad K where
  toFun v := f v • q
  map_add' v w := by simp only [map_add,add_smul]
  map_smul' k v := by simp only [map_smul,smul_eq_mul,mul_smul,RingHom.id_apply]

/-- The first three coordinates of the inverse of the actual dense frame. -/
def project (c g : V K) : V K →ₗ[K] Quad K :=
  interp c - along (defectCoef c g) (interp c g)

theorem project_apply (c g v : V K) :
    project c g v = interp c v - defectCoef c g v • interp c g := rfl

theorem defectCoef_sample (c g : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2) (q : Quad K) :
    defectCoef c g (sample c q) = 0 := by
  rw [defectCoef_apply,interp_sample c h01 h02 h12,sample_apply,sub_self,zero_div]

theorem project_sample (c g : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2) (q : Quad K) :
    project c g (sample c q) = q := by
  rw [project_apply,interp_sample c h01 h02 h12,
    defectCoef_sample c g h01 h02 h12,zero_smul,sub_zero]

theorem defectCoef_defect (c g : V K) (hp : pivot c g ≠ 0) :
    defectCoef c g g = 1 := by
  rw [defectCoef_apply]
  exact div_self hp

theorem project_defect (c g : V K) (hp : pivot c g ≠ 0) :
    project c g g = 0 := by
  rw [project_apply,defectCoef_defect c g hp,one_smul,sub_self]

/-- All-vector reconstruction, including the adjustable fourth row. -/
theorem reconstruct (c g v : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (i : Fin 4) :
    v i = ev (c i) (project c g v) + defectCoef c g v * g i := by
  obtain ⟨v0,v1,v2⟩ := interp_old c v h01 h02 h12
  obtain ⟨g0,g1,g2⟩ := interp_old c g h01 h02 h12
  have evp (j : Fin 4) :
      ev (c j) (project c g v) =
        ev (c j) (interp c v) - defectCoef c g v * ev (c j) (interp c g) := by
    simp only [project_apply,map_sub,map_smul,smul_eq_mul]
  rw [evp]
  fin_cases i
  · change v 0 = ev (c 0) (interp c v) - defectCoef c g v * ev (c 0) (interp c g) + defectCoef c g v * g 0
    rw [v0,g0]
    ring
  · change v 1 = ev (c 1) (interp c v) - defectCoef c g v * ev (c 1) (interp c g) + defectCoef c g v * g 1
    rw [v1,g1]
    ring
  · change v 2 = ev (c 2) (interp c v) - defectCoef c g v * ev (c 2) (interp c g) + defectCoef c g v * g 2
    rw [v2,g2]
    ring
  · change v 3 = ev (c 3) (interp c v) - defectCoef c g v * ev (c 3) (interp c g) + defectCoef c g v * g 3
    have hprod : defectCoef c g v * pivot c g = v 3 - ev (c 3) (interp c v) := by
      rw [defectCoef_apply,div_mul_cancel₀ _ hp]
    unfold pivot at hprod
    linear_combination -hprod

/-- Exact left inverse in both coordinates, not an arbitrary interpolation. -/
theorem coordinates_of_frame (c g : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (q : Quad K) (a : K) :
    project c g (sample c q + a • g) = q ∧
    defectCoef c g (sample c q + a • g) = a := by
  constructor <;> simp only [map_add,map_smul,project_sample c g h01 h02 h12,
    project_defect c g hp,defectCoef_sample c g h01 h02 h12,defectCoef_defect c g hp,
    smul_zero,add_zero,smul_eq_mul,mul_one,zero_add]

def toPoly : Quad K →ₗ[K] Polynomial K where
  toFun q := q.1 • (1 : Polynomial K) + q.2.1 • Polynomial.X + q.2.2 • (Polynomial.X^2)
  map_add' p q := by
    change (p.1+q.1) • (1 : Polynomial K) + (p.2.1+q.2.1) • Polynomial.X +
      (p.2.2+q.2.2) • (Polynomial.X^2) =
      (p.1 • (1 : Polynomial K) + p.2.1 • Polynomial.X + p.2.2 • (Polynomial.X^2)) +
      (q.1 • (1 : Polynomial K) + q.2.1 • Polynomial.X + q.2.2 • (Polynomial.X^2))
    simp only [add_smul]
    abel
  map_smul' k q := by
    change (k*q.1) • (1 : Polynomial K) + (k*q.2.1) • Polynomial.X +
      (k*q.2.2) • (Polynomial.X^2) =
      k • (q.1 • (1 : Polynomial K) + q.2.1 • Polynomial.X + q.2.2 • (Polynomial.X^2))
    simp only [mul_smul,smul_add]

theorem toPoly_apply (q : Quad K) :
    toPoly q = q.1 • (1 : Polynomial K) + q.2.1 • Polynomial.X +
      q.2.2 • (Polynomial.X^2) := rfl

def polyProject (c g : V K) : V K →ₗ[K] Polynomial K := toPoly.comp (project c g)

theorem evaluate_toPoly (E : Polynomial K →ₗ[K] K) (x : K)
    (h0 : E 1 = 1) (h1 : E Polynomial.X = x) (h2 : E (Polynomial.X^2) = x^2)
    (q : Quad K) : E (toPoly q) = ev x q := by
  simp only [toPoly_apply,map_add,map_smul,h0,h1,h2,smul_eq_mul,mul_one,ev_apply]

def prim (x : K) (q : Quad K) : K :=
  q.1*x + q.2.1*(x^2/2) + q.2.2*(x^3/3)

theorem primitive_evaluate_toPoly (IE : Polynomial K →ₗ[K] K) (x : K)
    (h0 : IE 1 = x) (h1 : IE Polynomial.X = x^2/2) (h2 : IE (Polynomial.X^2) = x^3/3)
    (q : Quad K) : IE (toPoly q) = prim x q := by
  simp only [toPoly_apply,map_add,map_smul,h0,h1,h2,smul_eq_mul,prim]

theorem polyProject_frame (c g : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) :
    polyProject c g 1 = 1 ∧ polyProject c g c = Polynomial.X ∧
    polyProject c g (c^2) = Polynomial.X^2 ∧ polyProject c g g = 0 := by
  have s0 : sample c ((1,0,0) : Quad K) = 1 := by
    funext i
    simp [sample_apply,ev_apply]
  have s1 : sample c ((0,1,0) : Quad K) = c := by
    funext i
    simp [sample_apply,ev_apply]
  have s2 : sample c ((0,0,1) : Quad K) = c^2 := by
    funext i
    simp [sample_apply,ev_apply,Pi.pow_apply]
  refine ⟨?_,?_,?_,?_⟩
  · change toPoly (project c g 1) = 1
    rw [←s0,project_sample c g h01 h02 h12]
    simp [toPoly_apply]
  · change toPoly (project c g c) = Polynomial.X
    rw [congrArg (fun v => toPoly (project c g v)) s1.symm, project_sample c g h01 h02 h12]
    simp [toPoly_apply]
  · change toPoly (project c g (c^2)) = Polynomial.X^2
    rw [←s2,project_sample c g h01 h02 h12]
    simp [toPoly_apply]
  · change toPoly (project c g g) = 0
    rw [project_defect c g hp,map_zero]

/-- Four reviewed Φ columns, not a new tree model or arbitrary input basis. -/
theorem reviewed_four_columns (G : Matrix (Fin 4) (Fin 4) K) (c g : V K)
    (h1 : G *ᵥ (1 : V K) = c)
    (hc : G *ᵥ c = (2 : K)⁻¹ • (c^2) + g) :
    Φ .leaf G = 1 ∧ Φ (.leaf ◂ .leaf) G = c ∧
    Φ ((.leaf ◂ .leaf) ◂ .leaf) G = c^2 ∧
    Φ (.leaf ◂ (.leaf ◂ .leaf)) G = (2 : K)⁻¹ • (c^2) + g := by
  have ht : Φ (.leaf ◂ .leaf) G = c := by
    change (1 : V K) * (G *ᵥ (1 : V K)) = c
    rw [h1,one_mul]
  refine ⟨rfl,ht,?_,?_⟩
  · change Φ (.leaf ◂ .leaf) G * (G *ᵥ (1 : V K)) = c^2
    rw [ht,h1,pow_two]
  · change (1 : V K) * (G *ᵥ Φ (.leaf ◂ .leaf) G) = _
    rw [one_mul,ht,hc]

/-- The actual shifted evaluation on the retained forward anchor. -/
theorem clean_anchor_all_vectors (c g v : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (hg : g 2 = 0) :
    ev (c 2) (project c g v) = v 2 := by
  symm
  simpa only [hg,mul_zero,add_zero] using reconstruct c g v h01 h02 h12 hp 2

/-- Exact all-vector equation for the original tilted covector
(A_d, B'_d, 0, 1). Only its zero on g is needed for this equation. -/
theorem clean_tilt_all_vectors (c g v : V K) (A B : K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (hzero : A*g 0 + B*g 1 + g 3 = 0) :
    A * ev (c 0) (project c g v) + B * ev (c 1) (project c g v) +
      ev (c 3) (project c g v) = A*v 0+B*v 1+v 3 := by
  let q := project c g v
  let a := defectCoef c g v
  have e0 : v 0 = ev (c 0) q + a*g 0 := reconstruct c g v h01 h02 h12 hp 0
  have e1 : v 1 = ev (c 1) q + a*g 1 := reconstruct c g v h01 h02 h12 hp 1
  have e3 : v 3 = ev (c 3) q + a*g 3 := reconstruct c g v h01 h02 h12 hp 3
  calc
    A * ev (c 0) (project c g v) + B * ev (c 1) (project c g v) +
        ev (c 3) (project c g v) =
      A*(ev (c 0) q+a*g 0)+B*(ev (c 1) q+a*g 1)+(ev (c 3) q+a*g 3) := by
        change A*ev (c 0) q+B*ev (c 1) q+ev (c 3) q = _
        linear_combination -a*hzero
    _ = A*v 0+B*v 1+v 3 := by rw [←e0,←e1,←e3]

/-- Feed the four exact local-three row actions, then the corrected row
identity is an identity on every actual stage vector. -/
theorem corrected_anchor_all_vectors (c g v : V K) (row : V K →ₗ[K] K) (γ : K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (hg : g 2 = 0)
    (h0 : row 1 = c 2) (h1 : row c = (c 2)^2/2)
    (h2 : row (c^2) = (c 2)^3/3) (hd : row g = 0) :
    row v-γ*v 2 =
      prim (c 2) (project c g v)-γ*ev (c 2) (project c g v) := by
  let q := project c g v
  let a := defectCoef c g v
  have hv : v = q.1 • (1 : V K) + q.2.1 • c + q.2.2 • (c^2) + a • g := by
    funext i
    simpa only [Pi.add_apply,Pi.smul_apply,Pi.one_apply,Pi.pow_apply,smul_eq_mul,
      mul_one,ev_apply,q,a] using reconstruct c g v h01 h02 h12 hp i
  have hr : row v = prim (c 2) q := by
    calc
      row v = row (q.1 • (1 : V K) + q.2.1 • c + q.2.2 • (c^2) + a • g) :=
        congrArg row hv
      _ = _ := by simp only [map_add,map_smul,h0,h1,h2,hd,smul_eq_mul,mul_zero,add_zero,prim]
  rw [hr,clean_anchor_all_vectors c g v h01 h02 h12 hp hg]

/-- Literal normalized coefficients of the second forward clean row. -/
def tiltA (a d g0 gd : K) : K := ((d-a)*gd)/((a-1)*g0)
def tiltB (a d g1 gd : K) : K := -((d-1)*gd)/((a-1)*g1)

theorem literal_tilt_annihilates (γ a d g0 g1 gd : K)
    (ha : a-1 ≠ 0) (h0 : g0 ≠ 0) (h1 : g1 ≠ 0) :
    let A := tiltA a d g0 gd
    let B := tiltB a d g1 gd
    A*(γ^2*g0)+B*(γ^2*g1)+γ^2*gd = 0 ∧
    A*(γ^3*g0)+B*(γ^3*a*g1)+γ^3*d*gd = 0 := by
  dsimp [tiltA,tiltB]
  constructor <;> field_simp [ha,h0,h1] <;> ring

/-- The normalized common seed's exact third row. The proof clears only
h-2, 2 and 3, and uses the seed polynomial, not a node evaluation. -/
theorem normalized_third_anchor [CharZero K] (h : K) (hn : h-2 ≠ 0)
    (hseed : 4*h^3-12*h^2+3*h+2=0) :
    let a := 1+h
    let s := 1+2*h
    let v := 2/(h-2)
    (2*h-v)+v+1=s ∧
    (2*h-v)+v*a+s=s^2/2 ∧
    (2*h-v)+v*a^2+s^2=s^3/3 ∧
    (2*h-v)/2+v*(1/2+h-h^2/2)=0 := by
  dsimp
  set a : K := 1+h with ha
  set s : K := 1+2*h with hs
  set v : K := 2/(h-2) with hv
  have E1 :
      (2*(h-2))*((2*h-v)+v*a+s-s^2/2) = -(4*h^3-12*h^2+3*h+2) := by
    rw [ha,hs,hv]
    field_simp [hn] <;> ring
  have E2 :
      (3*(h-2))*((2*h-v)+v*a^2+s^2-s^3/3) =
        -2*(h+1)*(4*h^3-12*h^2+3*h+2) := by
    rw [ha,hs,hv]
    field_simp [hn] <;> ring
  rw [hseed,neg_zero] at E1
  rw [hseed,mul_zero] at E2
  have d1 := (mul_eq_zero.mp E1).resolve_left (mul_ne_zero (by norm_num) hn)
  have d2 := (mul_eq_zero.mp E2).resolve_left (mul_ne_zero (by norm_num) hn)
  refine ⟨?_,sub_eq_zero.mp d1,sub_eq_zero.mp d2,?_⟩
  · rw [hs]
    ring
  · rw [hv]
    field_simp [hn] <;> ring

theorem normalized_second_row [CharZero K] (h : K) :
    let a := 1+h
    let g1 := 1/2+h-h^2/2
    h+a-a^2/2=g1 ∧ h+a^2-a^3/3=(2/3)*(h/2+(1+a)*g1) := by
  dsimp
  constructor <;> ring

/-- The last two rows of the actual Cramer system, proved once as exact
moment identities for the appended forward stage. -/
theorem normalized_fourth_moments [CharZero K] (d η U V W : K) (hη : η ≠ 0)
    (hV : (3/2)*V-W-(1+d)*U = -d*(d-1))
    (hW : (d-1)*U-η*W = -(d-1)*(d-d^2/2)) :
    let gd := d-d^2/2+U
    W=(d-1)*gd/η ∧ V+d^2=d^3/3+(2/3)*(W+gd+d*gd) := by
  dsimp
  constructor
  · apply (eq_div_iff hη).2
    linear_combination -hW
  · linear_combination (2/3 : K)*hV

theorem project_reviewed_four_columns (G : Matrix (Fin 4) (Fin 4) K) (c g : V K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2) (hp : pivot c g ≠ 0)
    (h1 : G *ᵥ (1 : V K) = c)
    (hc : G *ᵥ c = (2 : K)⁻¹ • (c^2) + g) :
    polyProject c g (Φ .leaf G) = 1 ∧
    polyProject c g (Φ (.leaf ◂ .leaf) G) = Polynomial.X ∧
    polyProject c g (Φ ((.leaf ◂ .leaf) ◂ .leaf) G) = Polynomial.X^2 ∧
    polyProject c g (Φ (.leaf ◂ (.leaf ◂ .leaf)) G) = (2 : K)⁻¹ • (Polynomial.X^2) := by
  obtain ⟨e0,e1,e2,e3⟩ := reviewed_four_columns G c g h1 hc
  obtain ⟨p0,p1,p2,pg⟩ := polyProject_frame c g h01 h02 h12 hp
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [e0,e1,e2,e3,p0,p1,p2,pg,map_add,map_smul,add_zero]

/-- The exact original polynomial covectors and the shifted anchor row.
The monomial tests bind E to evaluations and IE to the primitive evaluation. -/
theorem original_polynomial_covectors (c g v : V K) (A B γ : K)
    (E : Fin 4 → Polynomial K →ₗ[K] K) (IE : Polynomial K →ₗ[K] K)
    (row : V K →ₗ[K] K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (hg2 : g 2 = 0)
    (hzero : A*g 0+B*g 1+g 3 = 0)
    (hE : ∀ i, E i 1=1 ∧ E i Polynomial.X=c i ∧ E i (Polynomial.X^2)=(c i)^2)
    (hI0 : IE 1 = c 2) (hI1 : IE Polynomial.X = (c 2)^2/2)
    (hI2 : IE (Polynomial.X^2) = (c 2)^3/3)
    (h0 : row 1 = c 2) (h1 : row c = (c 2)^2/2)
    (h2 : row (c^2) = (c 2)^3/3) (hd : row g = 0) :
    E 2 (polyProject c g v) = v 2 ∧
    A*E 0 (polyProject c g v)+B*E 1 (polyProject c g v)+E 3 (polyProject c g v) =
      A*v 0+B*v 1+v 3 ∧
    row v-γ*v 2 = IE (polyProject c g v)-γ*E 2 (polyProject c g v) := by
  have e (i : Fin 4) : E i (polyProject c g v) = ev (c i) (project c g v) := by
    obtain ⟨e0,e1,e2⟩ := hE i
    exact evaluate_toPoly (E i) (c i) e0 e1 e2 (project c g v)
  have ie : IE (polyProject c g v) = prim (c 2) (project c g v) :=
    primitive_evaluate_toPoly IE (c 2) hI0 hI1 hI2 (project c g v)
  simp only [e,ie]
  exact ⟨clean_anchor_all_vectors c g v h01 h02 h12 hp hg2,
    clean_tilt_all_vectors c g v A B h01 h02 h12 hp hzero,
    corrected_anchor_all_vectors c g v row γ h01 h02 h12 hp hg2 h0 h1 h2 hd⟩

/-- Once a literal raw column differs from the intended polynomial evaluation
by a combination of g and cg, both original clean constraints vanish on
the actual projected defect. No degree check is hidden in this step. -/
theorem projected_defect_clean (c g v : V K) (A B α β : K)
    (E : Fin 4 → Polynomial K →ₗ[K] K) (H P : Polynomial K)
    (hanchor : E 2 P = v 2) (htilt : A*E 0 P+B*E 1 P+E 3 P = A*v 0+B*v 1+v 3)
    (hg2 : g 2=0) (hg : A*g 0+B*g 1+g 3=0)
    (hcg : A*c 0*g 0+B*c 1*g 1+c 3*g 3=0)
    (hV : ∀ i, v i = E i H+α*g i+β*c i*g i) :
    E 2 (H-P)=0 ∧ A*E 0 (H-P)+B*E 1 (H-P)+E 3 (H-P)=0 := by
  constructor
  · simp only [map_sub,hanchor,hV,hg2,mul_zero,add_zero,sub_self]
  · rw [hV 0,hV 1,hV 3] at htilt
    simp only [map_sub]
    linear_combination -htilt - α*hg - β*hcg

end RKResearch.Certified.PaidDefectBridge.ForwardChart
