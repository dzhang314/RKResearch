module

public import RKCert.ERKOrderNineH48DiagData
public import RKCert.RootTupleSpecialization

@[expose] public section

namespace RKCert.GoodPrimeDense
open RKCert.FixedFactor

theorem map_read {A R S : Type*} [CommRing R] [CommRing S] (g : R→+*S)
    (f : A→R) (x : R) (p : List A) :
    g (read f x p) = read (g ∘ f) (g x) p := by
  induction p with
  | nil => simp [read]
  | cons a p ih => simp [read,ih]

theorem read_congr {A R : Type*} [CommRing R] {f g : A→R}
    (e : ∀ a, f a=g a) (x : R) (t : List A) :
    read f x t=read g x t := by
  rw [funext e]

def diag0 {R : Type*} [CommRing R] (f : ℤ→R) (l h u v : R) : R :=
  read (read (read (read f l) h) u) v intStage0

def diag1 {R : Type*} [CommRing R] (f : ℤ→R) (l h u : R) : R :=
  read (read (read f l) h) u intStage1

def diag2 {R : Type*} [CommRing R] (f : ℤ→R) (l h : R) : R :=
  read (read f l) h intStage2

noncomputable def diagPoly0 : MvPolynomial (Fin 4) ℤ :=
  diag0 (Int.castRingHom _) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3)

noncomputable def diagPoly1 : MvPolynomial (Fin 4) ℤ :=
  diag1 (Int.castRingHom _) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

noncomputable def diagPoly2 : MvPolynomial (Fin 4) ℤ :=
  diag2 (Int.castRingHom _) (MvPolynomial.X 0) (MvPolynomial.X 1)

noncomputable def diagAux : Fin 3 → MvPolynomial (Fin 4) ℤ :=
  ![diagPoly0,diagPoly1,diagPoly2]

variable {R : Type*} [CommRing R]

theorem zEval_diagPoly0 (l h u v : R) :
    zEval diagPoly0 ![l,h,u,v] = diag0 (Int.castRingHom R) l h u v := by
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom R) (![l,h,u,v] : Fin 4→R)
  change ψ diagPoly0 = _
  simp only [diagPoly0,diag0,map_read ψ,Function.comp_def]
  simp [ψ]

theorem zEval_diagPoly1 (l h u v : R) :
    zEval diagPoly1 ![l,h,u,v] = diag1 (Int.castRingHom R) l h u := by
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom R) (![l,h,u,v] : Fin 4→R)
  change ψ diagPoly1 = _
  simp only [diagPoly1,diag1,map_read ψ,Function.comp_def]
  simp [ψ]

theorem zEval_diagPoly2 (l h u v : R) :
    zEval diagPoly2 ![l,h,u,v] = diag2 (Int.castRingHom R) l h := by
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom R) (![l,h,u,v] : Fin 4→R)
  change ψ diagPoly2 = _
  simp only [diagPoly2,diag2,map_read ψ,Function.comp_def]
  simp [ψ]

def computeHorner {A B : Type*} (o : Operations A) (f : B→A) (x : A) : List B → A
  | [] => o.zero
  | b :: q => o.add (f b) (o.mul x (computeHorner o f x q))

theorem computeHorner_sound {A B : Type*} {o : Operations A} {φ : A→R}
    (s : Sound o φ) (f : B→A) (x : A) (L : List B) :
    φ (computeHorner o f x L) = read (φ ∘ f) (φ x) L := by
  induction L with
  | nil => exact s.zero
  | cons a L ih => simp only [computeHorner,s.add,s.mul,read,Function.comp_apply,ih]

def diagRecipe0 {A : Type*} (o : Operations A) (l h u v : A) : A :=
  computeHorner o (computeHorner o (computeHorner o (computeHorner o o.int l) h) u) v intStage0

def diagRecipe1 {A : Type*} (o : Operations A) (l h u : A) : A :=
  computeHorner o (computeHorner o (computeHorner o o.int l) h) u intStage1

def diagRecipe2 {A : Type*} (o : Operations A) (l h : A) : A :=
  computeHorner o (computeHorner o o.int l) h intStage2

theorem diagRecipe0_eval {A : Type*} {o : Operations A} {φ : A→R}
    (s : Sound o φ) (l h u v : A) :
    φ (diagRecipe0 o l h u v) = diag0 (Int.castRingHom R) (φ l) (φ h) (φ u) (φ v) := by
  simp [diagRecipe0,diag0,computeHorner_sound s,Function.comp_def,s.int]

theorem diagRecipe1_eval {A : Type*} {o : Operations A} {φ : A→R}
    (s : Sound o φ) (l h u : A) :
    φ (diagRecipe1 o l h u) = diag1 (Int.castRingHom R) (φ l) (φ h) (φ u) := by
  simp [diagRecipe1,diag1,computeHorner_sound s,Function.comp_def,s.int]

theorem diagRecipe2_eval {A : Type*} {o : Operations A} {φ : A→R}
    (s : Sound o φ) (l h : A) :
    φ (diagRecipe2 o l h) = diag2 (Int.castRingHom R) (φ l) (φ h) := by
  simp [diagRecipe2,diag2,computeHorner_sound s,Function.comp_def,s.int]

end RKCert.GoodPrimeDense
