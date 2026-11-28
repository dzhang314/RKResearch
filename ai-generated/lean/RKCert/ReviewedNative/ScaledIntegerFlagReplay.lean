module

public import RKCert.ReviewedNative.RationalFlagReplay
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Integer-only replay of graded sufficient flags

The numerical checks are integer dot products, matrix actions, and
componentwise products. The proof interprets the supplied spans over
the rationals, then recovers every integer numerator moment by
injectivity. Basis/projection denominators never become requirements
on the final coefficient ring. -/
namespace RKResearch.Certified.ScaledIntegerFlagReplay

open RKResearch Graded FiniteRootedTree
open scoped Matrix BigOperators

abbrev VI (s : Nat) := Fin s → ℤ
abbrev V (s : Nat) := Fin s → ℚ
variable {s : Nat}

structure Packet (s : Nat) where
  a : Fin s → Fin s → ℤ
  w : VI s
  clock : VI s
  stageScale : ℤ
  weightScale : ℤ
  size : Nat → Nat
  pivot : (k : Nat) → Fin (size k) → Fin s
  basis : (k : Nat) → Fin (size k) → VI s
  spanScale : Nat → ℤ
  liftCoeff : (k : Nat) → Fin (size k) → ℤ

def matrix (P : Packet s) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if i < j then 0 else P.a i j

theorem lower (P : Packet s) : (matrix P).IsLowerTriangular := by
  intro i j h
  change i < j at h
  simp [matrix,h]

/-- Small recursive arithmetic view of a finite sum. -/
def isum : {n : Nat} → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n+1, f => f 0 + isum (fun j : Fin n => f j.succ)

theorem isum_eq {n : Nat} (f : Fin n → ℤ) : isum f = ∑ j,f j := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp only [isum,ih,Fin.sum_univ_succ]

def act (P : Packet s) (v : VI s) : VI s :=
  fun i => isum fun j => matrix P i j * v j

def output (P : Packet s) (v : VI s) : ℤ :=
  isum fun i => P.w i*v i

theorem act_eq (P : Packet s) (v : VI s) : act P v = matrix P *ᵥ v := by
  funext i
  simp only [act,isum_eq,Matrix.mulVec_apply_eq_sum]

theorem output_eq (P : Packet s) (v : VI s) : output P v = P.w ⬝ᵥ v := by
  simp only [output,isum_eq,dotProduct]

def eqV (v w : VI s) : Bool := (List.finRange s).all fun i => decide (v i=w i)

theorem eq_of_eqV {v w : VI s} (h : eqV v w=true) : v=w :=
  funext fun i => of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

def project (P : Packet s) (k : Nat) (v : VI s) : VI s :=
  fun i => isum fun j : Fin (P.size k) =>
    (v (P.pivot k j)*P.liftCoeff k j)*P.basis k j i

def checkMember (P : Packet s) (k : Nat) (v : VI s) : Bool :=
  eqV (P.spanScale k • v) (project P k v)

def primitive (P : Packet s) (k : Nat) : VI s :=
  ((k+1:Nat):ℤ) • act P (P.clock^k)-P.clock^(k+1)

def checkNode (P : Packet s) : Bool := eqV (act P 1) P.clock

def checkA (P : Packet s) (k : Nat) (i : Fin (P.size k)) : Bool :=
  checkMember P (k+1) (act P (P.basis k i))

def checkC (P : Packet s) (k : Nat) (i : Fin (P.size k)) : Bool :=
  checkMember P (k+1) (P.clock*P.basis k i)

def checkProduct (P : Packet s) (k l : Nat)
    (i : Fin (P.size k)) (j : Fin (P.size l)) : Bool :=
  checkMember P (k+l) (P.basis k i*P.basis l j)

def checkPrimitive (P : Packet s) (k : Nat) : Bool :=
  checkMember P (k+1) (primitive P k)

def checkSilent (P : Packet s) (k : Nat) (i : Fin (P.size k)) : Bool :=
  decide (output P (P.basis k i)=0)

def checkScalar (P : Packet s) (k : Nat) : Bool :=
  decide (((k+1:Nat):ℤ)*output P (P.clock^k)=P.weightScale*P.stageScale^k)

structure Receipts (p : Nat) (P : Packet s) : Prop where
  stage_ne : P.stageScale≠0
  weight_ne : P.weightScale≠0
  scale_ne : ∀ k, k<p → P.spanScale k≠0
  node : checkNode P=true
  stepA : ∀ k, k+1<p → ∀ i, checkA P k i=true
  stepC : ∀ k, k+1<p → ∀ i, checkC P k i=true
  product : ∀ k l, k+l<p → ∀ i j, checkProduct P k l i j=true
  primitive : ∀ k, k+1<p → checkPrimitive P k=true
  silent : ∀ k, k<p → ∀ i, checkSilent P k i=true
  scalar : ∀ k, k<p → checkScalar P k=true

def toQ (v : VI s) : V s := Int.castRingHom ℚ ∘ v

@[simp] theorem toQ_apply (v : VI s) (i : Fin s) : toQ v i=(v i:ℚ) := rfl

theorem toQ_one : toQ (1:VI s)=1 := by funext i; simp
theorem toQ_mul (u v : VI s) : toQ (u*v)=toQ u*toQ v := by
  funext i
  simp
theorem toQ_pow (v : VI s) (k : Nat) : toQ (v^k)=toQ v^k := by
  funext i
  simp
theorem toQ_sub (u v : VI s) : toQ (u-v)=toQ u-toQ v := by
  funext i
  simp
theorem toQ_smul (a : ℤ) (v : VI s) : toQ (a • v)=(a:ℚ) • toQ v := by
  funext i
  simp only [toQ_apply,Pi.smul_apply,smul_eq_mul,Int.cast_mul]

def A (P : Packet s) : Matrix (Fin s) (Fin s) ℚ :=
  (P.stageScale:ℚ)⁻¹ • (matrix P).map (Int.castRingHom ℚ)

def b (P : Packet s) : V s :=
  (P.weightScale:ℚ)⁻¹ • toQ P.w

theorem action (P : Packet s) (v : VI s) :
    mat (A P) (toQ v)=(P.stageScale:ℚ)⁻¹ • toQ (act P v) := by
  rw [act_eq]
  simp only [A,mat_apply,Matrix.smul_mulVec]
  congr 1
  funext i
  exact ((Int.castRingHom ℚ).map_mulVec (matrix P) v i).symm

theorem readout (P : Packet s) (v : VI s) :
    row (b P) (toQ v)=(P.weightScale:ℚ)⁻¹*(output P v:ℚ) := by
  rw [output_eq,row_apply,b,smul_dotProduct,smul_eq_mul]
  congr 1
  exact ((Int.castRingHom ℚ).map_dotProduct P.w v).symm

variable {P : Packet s} {p : Nat}

theorem nodes_eq (h : Receipts p P) :
    nodes (A P)=(P.stageScale:ℚ)⁻¹ • toQ P.clock := by
  change mat (A P) (1:V s)=_
  rw [←toQ_one,action,eq_of_eqV h.node]

def band (P : Packet s) (k : Nat) : Submodule ℚ (V s) :=
  Submodule.span ℚ (Set.range (toQ ∘ P.basis k))

theorem member_of_check {k : Nat} {v : VI s} (hn : P.spanScale k≠0)
    (h : checkMember P k v=true) : toQ v∈band P k := by
  have he := eq_of_eqV h
  have ec : (P.spanScale k:ℚ) • toQ v =
      ∑ j : Fin (P.size k), ((v (P.pivot k j)*P.liftCoeff k j:ℤ):ℚ) •
        toQ (P.basis k j) := by
    funext i
    have hi := congrArg (Int.castRingHom ℚ) (congrFun he i)
    simpa only [project,isum_eq,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,
      map_sum,map_mul,Int.cast_mul,Int.coe_castRingHom,toQ_apply] using hi
  have hmem : (P.spanScale k:ℚ) • toQ v∈band P k := by
    rw [ec]
    exact Submodule.sum_mem _ fun j _ =>
      (band P k).smul_mem _ (Submodule.subset_span ⟨j,rfl⟩)
  have q := (band P k).smul_mem ((P.spanScale k:ℚ)⁻¹) hmem
  rw [smul_smul,inv_mul_cancel₀ (Int.cast_ne_zero.mpr hn),one_smul] at q
  exact q

theorem primitive_scale (h : Receipts p P) (k : Nat) :
    ((k+1:Nat):ℚ) • mat (A P) ((nodes (A P))^k)-(nodes (A P))^(k+1)=
      ((P.stageScale:ℚ)⁻¹)^(k+1) • toQ (primitive P k) := by
  simp only [nodes_eq h,smul_pow,←toQ_pow,map_smul,action,primitive,toQ_sub,
    toQ_smul,Int.cast_natCast,smul_sub,smul_smul]
  rw [pow_succ]
  funext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

noncomputable def sufficient (h : Receipts p P) : SufficientFlags p (A P) (b P) := by
  refine ⟨band P,?_,?_,?_,?_,?_,?_⟩
  · intro k hk v hv
    have e : band P k ≤ (band P (k+1)).comap (mat (A P)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change mat (A P) (toQ (P.basis k i))∈band P (k+1)
      rw [action]
      exact (band P (k+1)).smul_mem _ (member_of_check (h.scale_ne _ hk) (h.stepA _ hk i))
    exact e hv
  · intro k hk v hv
    have e : band P k ≤ (band P (k+1)).comap (diag (nodes (A P))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change nodes (A P)*toQ (P.basis k i)∈band P (k+1)
      rw [nodes_eq h,smul_mul_assoc,←toQ_mul]
      exact (band P (k+1)).smul_mem _ (member_of_check (h.scale_ne _ hk) (h.stepC _ hk i))
    exact e hv
  · intro k l hkl v u hv hu
    apply RationalFlagReplay.span_mul_mem _ hv hu
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    change toQ (P.basis k i)*toQ (P.basis l j)∈band P (k+l)
    rw [←toQ_mul]
    exact member_of_check (h.scale_ne _ hkl) (h.product _ _ hkl i j)
  · intro k hk
    rw [primitive_scale h]
    exact (band P (k+1)).smul_mem _ (member_of_check (h.scale_ne _ hk) (h.primitive _ hk))
  · intro k hk v hv
    have e : band P k ≤ (row (b P)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change row (b P) (toQ (P.basis k i))=0
      rw [readout,of_decide_eq_true (h.silent _ hk i),Int.cast_zero,mul_zero]
    exact e hv
  · intro k hk
    have z : ((k+1:Nat):ℤ)*output P (P.clock^k)=P.weightScale*P.stageScale^k :=
      of_decide_eq_true (h.scalar _ hk)
    have eq := congrArg (Int.castRingHom ℚ) z
    simp only [map_mul,map_natCast,map_pow,Int.coe_castRingHom] at eq
    have dw : (P.weightScale:ℚ)*(P.weightScale:ℚ)⁻¹=1 :=
      mul_inv_cancel₀ (Int.cast_ne_zero.mpr h.weight_ne)
    have da : (P.stageScale:ℚ)^k*((P.stageScale:ℚ)⁻¹)^k=1 := by
      rw [←mul_pow,mul_inv_cancel₀ (Int.cast_ne_zero.mpr h.stage_ne),one_pow]
    rw [nodes_eq h,smul_pow,←toQ_pow,map_smul,smul_eq_mul,readout]
    calc
      _ = (((k+1:Nat):ℚ)*(output P (P.clock^k):ℚ))*
          ((P.weightScale:ℚ)⁻¹*((P.stageScale:ℚ)⁻¹)^k) := by ring
      _ = (P.weightScale:ℚ)*(P.weightScale:ℚ)⁻¹*
          ((P.stageScale:ℚ)^k*((P.stageScale:ℚ)⁻¹)^k) := by rw [eq]; ring
      _ = 1 := by rw [dw,da,one_mul]

theorem order (h : Receipts p P) : HasOrder p (A P) (b P) :=
  (sufficient h).hasOrder

theorem paid_moment (h : Receipts p P) (t : FiniteRootedTree) (ht : (t.order:Nat)≤p) :
    (t.factorial:ℤ)*(P.w ⬝ᵥ Φ t (matrix P))=P.weightScale*P.stageScale^((t.order:Nat)-1) := by
  let f := Int.castRingHom ℚ
  have hA : (matrix P).map f = f P.stageScale • A P := by
    change _ = (P.stageScale:ℚ) • ((P.stageScale:ℚ)⁻¹ • (matrix P).map f)
    rw [smul_smul,mul_inv_cancel₀ (Int.cast_ne_zero.mpr h.stage_ne),one_smul]
  have hb : f ∘ P.w = f P.weightScale • b P := by
    change _ = (P.weightScale:ℚ) • ((P.weightScale:ℚ)⁻¹ • (f∘P.w))
    rw [smul_smul,mul_inv_cancel₀ (Int.cast_ne_zero.mpr h.weight_ne),one_smul]
  apply (Int.cast_injective (α:=ℚ))
  change f _ = f _
  simp only [map_mul,map_natCast,map_pow,RingHom.map_dotProduct,map_Φ,hA,hb,
    Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  have e := order h t ht
  calc
    _ = (f P.weightScale*(f P.stageScale)^((t.order:Nat)-1))*
        ((t.factorial:ℚ)*(b P ⬝ᵥ Φ t (A P))) := by ring
    _ = _ := by rw [e,mul_one]

section Target
variable {R : Type*} [CommRing R]

def normalizedA (P : Packet s) (u : R) : Matrix (Fin s) (Fin s) R :=
  u • (matrix P).map (Int.castRingHom R)

def normalizedB (P : Packet s) (v : R) : Fin s→R :=
  v • (Int.castRingHom R ∘ P.w)

theorem normalized_lower (P : Packet s) (u : R) : (normalizedA P u).IsLowerTriangular := by
  intro i j h
  change u * ((matrix P i j:ℤ):R)=0
  rw [lower P h,Int.cast_zero,mul_zero]

theorem transport (h : Receipts p P) (u v : R)
    (hu : (P.stageScale:R)*u=1) (hv : (P.weightScale:R)*v=1) :
    HasOrder p (normalizedA P u) (normalizedB P v) := by
  let f := Int.castRingHom R
  have hA : (matrix P).map f = f P.stageScale • normalizedA P u := by
    change _ = f P.stageScale • (u • (matrix P).map f)
    rw [smul_smul,show f P.stageScale*u=1 from hu,one_smul]
  have hb : f ∘ P.w = f P.weightScale • normalizedB P v := by
    change _ = f P.weightScale • (v • (f ∘ P.w))
    rw [smul_smul,show f P.weightScale*v=1 from hv,one_smul]
  exact hasOrder_of_scaled_moments f hA hb (IsUnit.of_mul_eq_one _ hu)
    (IsUnit.of_mul_eq_one _ hv) (paid_moment h)

end Target
end RKResearch.Certified.ScaledIntegerFlagReplay

#print axioms RKResearch.Certified.ScaledIntegerFlagReplay.paid_moment
#print axioms RKResearch.Certified.ScaledIntegerFlagReplay.transport
