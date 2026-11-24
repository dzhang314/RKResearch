module

public import RKCert.ERKOrderNineH48Bridge
public import RKCert.ERKOrderNineH48DiagnosticForms

@[expose] public section

/-! # The exact partial eliminants survive integer reduction -/
namespace RKCert.GoodPrimeDense
open RKCert.Paired RKCert.FixedFactor Polynomial

def lift1 (d : ℤ) (p : List ℤ) : List ℚ := p.map fun a => (a:ℚ)/(d:ℚ)
def lift2 (d : ℤ) (p : List (List ℤ)) : List (List ℚ) := p.map (lift1 d)
def lift3 (d : ℤ) (p : L2 (List ℤ)) : L2 (List ℚ) := p.map (lift2 d)
def lift4 (d : ℤ) (p : L3 (List ℤ)) : L3 (List ℚ) := p.map (lift3 d)

set_option maxRecDepth 4000 in
theorem matches0 : h48Stage0=lift4 stageDen0 intStage0 := by decide +kernel
set_option maxRecDepth 4000 in
theorem matches1 : h48Stage1=lift3 stageDen1 intStage1 := by decide +kernel
set_option maxRecDepth 4000 in
theorem matches2 : h48Stage2=lift2 stageDen2 intStage2 := by decide +kernel

theorem read_divCoeffList {K : Type*} [Field K] [CharZero K] (d : ℤ) (l : K) (r : List ℤ) :
    read (Rat.castHom K) l (lift1 d r) = ((d:K)⁻¹)*read (Int.castRingHom K) l r := by
  induction r with
  | nil => simp [lift1,read]
  | cons a r ih =>
    change read (Rat.castHom K) l (((a:ℚ)/(d:ℚ))::lift1 d r) =
      ((d:K)⁻¹)*read (Int.castRingHom K) l (a::r)
    simp only [read]
    rw [ih,map_div₀,map_intCast,map_intCast]
    simp only [Int.coe_castRingHom,div_eq_mul_inv]
    ring

theorem read_map_scaled {A B R : Type*} [CommRing R] (f : A→R) (g : B→R) (w : B→A)
    (k x : R) (e : ∀a,f (w a) = k*g a) (p : List B) :
    read f x (p.map w) = k*read g x p := by
  induction p with
  | nil => simp [read]
  | cons a p ih =>
    simp only [List.map_cons, read, e, ih]
    ring

theorem diag0_matches {K : Type*} [Field K] [CharZero K] (l h u v : K) :
    read (read (read (read (Rat.castHom K) l) h) u) v h48Stage0 =
      ((stageDen0:K)⁻¹)*diag0 (Int.castRingHom K) l h u v := by
  rw [matches0]
  unfold diag0 lift4
  apply read_map_scaled
  intro a
  unfold lift3
  apply read_map_scaled
  intro a
  unfold lift2
  apply read_map_scaled
  intro a
  apply read_divCoeffList

theorem diag1_matches {K : Type*} [Field K] [CharZero K] (l h u : K) :
    read (read (read (Rat.castHom K) l) h) u h48Stage1 =
      ((stageDen1:K)⁻¹)*diag1 (Int.castRingHom K) l h u := by
  rw [matches1]
  unfold diag1 lift3
  apply read_map_scaled
  intro a
  unfold lift2
  apply read_map_scaled
  intro a
  apply read_divCoeffList

theorem diag2_matches {K : Type*} [Field K] [CharZero K] (l h : K) :
    read (read (Rat.castHom K) l) h h48Stage2 =
      ((stageDen2:K)⁻¹)*diag2 (Int.castRingHom K) l h := by
  rw [matches2]
  unfold diag2 lift2
  apply read_map_scaled
  intro a
  apply read_divCoeffList

set_option maxHeartbeats 900000 in
theorem normStages_vanish {K : Type*} [Field K] [CharZero K] {h u v l : K}
    (root : RootSystem (pencilAt l ((84:K)⁻¹)) h u v)
    (z : sixOnK8 h u v l=0) :
    (∀j, zEval (diagAux j) ![l,h,u,v]=0) := by
  let f := read (Rat.castHom K) l
  let s : Sound (dense (scalar ℚ)) f := (Sound.scalar (Rat.castHom K)).dense l
  have fl : f exactParam = l := read_generator (Sound.scalar (Rat.castHom K)) l
  have fd : f exactInv = (84:K)⁻¹ := by
    change read (Rat.castHom K) l (constant (scalar ℚ) ((84:ℚ)⁻¹)) = _
    rw [read_constant (Sound.scalar (Rat.castHom K))]
    simp
  have r : RootSystem (exactTower.four.map f) h u v := by
    change RootSystem ((pencilRecipe (dense (scalar ℚ)) exactParam exactInv).map f) h u v
    rw [map_pencilRecipe s,fl,fd]
    exact root
  let fh := read f h
  let fu := read fh u
  let fv := read fu v
  have sh : Sound exactTower.atH fh := Tower.soundH s h r.four
  have su : Sound exactTower.atU fu := Tower.soundU s h u r.four r.three
  have sv : Sound exactTower.atV fv := Tower.soundV s h u v r
  have z0 : fv h48Stage0 = 0 := by
    rw [←h48_check0,eval_k8Recipe sv]
    have eqL : fv (exactTower.coe exactParam) = l :=
      (Tower.readCoe s h u v r exactParam).trans fl
    have eqH : fv exactTower.h=h := Tower.readH s h u v r
    have eqU : fv exactTower.u=u := Tower.readU s h u v r
    have eqV : fv exactTower.v=v := Tower.readV s h u v r
    have hr : fv exactR.value = 2-l-h-u-v := by
      change fv ((2-⟨exactTower.coe exactParam⟩-⟨exactTower.h⟩-⟨exactTower.u⟩-⟨exactTower.v⟩ :
        Box exactTower.atV).value) = _
      simp only [Box.cast_sub sv,Box.cast_num sv,Nat.cast_ofNat,eqL,eqH,eqU,eqV]
    rw [hr,show fv exactTower.h=h from Tower.readH s h u v r,
      show fv exactTower.u=u from Tower.readU s h u v r,
      show fv exactTower.v=v from Tower.readV s h u v r]
    exact z
  have vEq : fv exactTower.relV = v^2 := by
    change read fu v exactTower.relV = _
    simp only [Tower.relV,Two.rel,read,su.neg,mul_zero,add_zero]
    have hv := r.two
    rw [←Tower.read_quad s h u r.four r.three] at hv
    simp only [Two.eval,Two.map] at hv
    linear_combination -hv
  have uEq : fu exactTower.relU = u^3 := by
    change read fh u exactTower.relU = _
    simp only [Tower.relU,Three.rel,read,sh.neg,mul_zero,add_zero]
    have hu := r.three
    rw [←Tower.read_cubic s h r.four] at hu
    simp only [Three.eval,Three.map] at hu
    linear_combination -hu
  have z1 : fu h48Stage1 = 0 := by
    rw [←h48_check1]
    exact read_norm_eq_zero su v (n:=2) (by decide) rfl vEq h48Stage0 z0
  have z2 : fh h48Stage2 = 0 := by
    rw [←h48_check2]
    exact read_norm_eq_zero sh u (n:=3) (by decide) rfl uEq h48Stage1 z1
  change read (read (read (read (Rat.castHom K) l) h) u) v h48Stage0 = 0 at z0
  change read (read (read (Rat.castHom K) l) h) u h48Stage1 = 0 at z1
  change read (read (Rat.castHom K) l) h h48Stage2 = 0 at z2
  rw [diag0_matches] at z0
  rw [diag1_matches] at z1
  rw [diag2_matches] at z2
  intro j
  fin_cases j
  · change zEval diagPoly0 ![l,h,u,v]=0
    rw [zEval_diagPoly0]
    exact (mul_eq_zero.mp z0).resolve_left (by norm_num [stageDen0])
  · change zEval diagPoly1 ![l,h,u,v]=0
    rw [zEval_diagPoly1]
    exact (mul_eq_zero.mp z1).resolve_left (by norm_num [stageDen1])
  · change zEval diagPoly2 ![l,h,u,v]=0
    rw [zEval_diagPoly2]
    exact (mul_eq_zero.mp z2).resolve_left (by norm_num [stageDen2])

end RKCert.GoodPrimeDense
