module

public import RKCert.ReviewedNative.NativePencilProjectionLift
public import RKCert.ReviewedNative.NativeHornerWitness
public import Mathlib.Data.List.GetD
public import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Literal integer Horner data as nested scalar polynomials -/
namespace RKResearch.Certified.Graded.NativePencilProjection
open Polynomial NativeHornerWitness
noncomputable section

def pack {R : Type*} [CommRing R] (l : List R) : R[X] := horner (fun a => C a) X l

@[simp] theorem pack_nil {R : Type*} [CommRing R] : pack ([] : List R)=0 := rfl

theorem pack_cons {R : Type*} [CommRing R] (a : R) (l : List R) :
    pack (a::l)=C a+X*pack l := rfl

theorem pack_coeff {R : Type*} [CommRing R] (l : List R) (i : ℕ) :
    (pack l).coeff i=l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons c p ih =>
    cases i with
    | zero => simp [pack_cons]
    | succ i => simp [pack_cons,coeff_X_mul,ih]

theorem pack_bound {R : Type*} [CommRing R] (l : List R) (n : ℕ) (h : l.length≤n+1) :
    (pack l).natDegree≤n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pack_coeff]
  exact List.getD_eq_default _ _ (by omega)

abbrev packZ (l : List ℤ) : ZPoly := pack l
abbrev packT (l : List (List ℤ)) : TPoly := pack (l.map packZ)
abbrev packX (l : List (List (List ℤ))) : XPoly := pack (l.map packT)

theorem coeff_packT (l : List (List ℤ)) (i : ℕ) : (packT l).coeff i=packZ (l.getD i []) := by
  have h := List.getD_map (n:=i) l [] packZ
  simpa only [packT,pack_coeff,packZ,pack_nil] using h

theorem coeff_packX (l : List (List (List ℤ))) (i : ℕ) : (packX l).coeff i=packT (l.getD i []) := by
  have h := List.getD_map (n:=i) l [] packT
  simpa only [packX,pack_coeff,packT,List.map_nil,pack_nil] using h

theorem horner_map {D B k : Type*} [CommRing k] (f : B→k) (z : k) (g : D→B) (l : List D) :
    horner f z (l.map g)=horner (fun v => f (g v)) z l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,horner,ih]

theorem pack_eval {R k : Type*} [CommRing R] [CommRing k] (q : R→+*k) (z : k) (l : List R) :
    (pack l).eval₂ q z=horner (fun a => q a) z l := by
  induction l with
  | nil => simp [horner]
  | cons a l ih => simp only [pack_cons,eval₂_add,eval₂_mul,eval₂_X,eval₂_C,ih,horner]

abbrev foldZ {k : Type*} [CommRing k] (z : k) := horner (fun a : ℤ => (a:k)) z
abbrev foldT {k : Type*} [CommRing k] (z t : k) := horner (foldZ z) t
abbrev foldX {k : Type*} [CommRing k] (z t x : k) := horner (foldT z t) x

theorem eval_packZ {k : Type*} [Field k] (z : k) (l : List ℤ) :
    zEval z (packZ l) = foldZ z l := pack_eval (Int.castRingHom k) z l

theorem eval_packT {k : Type*} [Field k] (z t : k) (l : List (List ℤ)) :
    tEval z t (packT l) = foldT z t l := by
  change (pack (l.map packZ)).eval₂ (zEval z) t = _
  simp only [pack_eval,horner_map,eval_packZ,foldT]

theorem eval_packX {k : Type*} [Field k] (z t x : k) (l : List (List (List ℤ))) :
    (packX l).eval₂ (tEval z t) x = foldX z t x l := by
  simp only [packX,pack_eval,horner_map,eval_packT,foldX]

abbrev redZ (p : ℕ) (l : List ℤ) : List (ZMod p) := List.map (fun (a : ℤ) => (a : ZMod p)) l
abbrev redT (p : ℕ) (l : List (List ℤ)) := l.map (redZ p)
abbrev redX (p : ℕ) (l : List (List (List ℤ))) := l.map (redT p)

theorem foldZ_reduce {k : Type*} [CommRing k] {p : ℕ} (q : ZMod p →+* k) (z : k) (l : List ℤ) :
    foldZ z l = horner (fun a => q a) z (redZ p l) := by
  change horner (fun a : ℤ => (a : k)) z l =
    horner (fun a => q a) z (l.map (fun a : ℤ => (a : ZMod p)))
  rw [horner_map]
  apply congrArg (fun f => horner f z l)
  funext a
  exact (map_intCast q a).symm

theorem foldT_reduce {k : Type*} [CommRing k] {p : ℕ} (q : ZMod p →+* k) (z t : k) (l : List (List ℤ)) :
    foldT z t l = horner (horner (fun a => q a) z) t (redT p l) := by
  change horner (foldZ z) t l = horner (horner (fun a => q a) z) t (l.map (redZ p))
  rw [horner_map]
  apply congrArg (fun f => horner f t l)
  funext a
  exact foldZ_reduce q z a

theorem foldX_reduce {k : Type*} [CommRing k] {p : ℕ} (q : ZMod p →+* k) (z t x : k) (l : List (List (List ℤ))) :
    foldX z t x l = horner (horner (horner (fun a => q a) z) t) x (redX p l) := by
  change horner (foldT z t) x l = horner (horner (horner (fun a => q a) z) t) x (l.map (redT p))
  rw [horner_map]
  apply congrArg (fun f => horner f x l)
  funext a
  exact foldT_reduce q z t a

end
end RKResearch.Certified.Graded.NativePencilProjection
