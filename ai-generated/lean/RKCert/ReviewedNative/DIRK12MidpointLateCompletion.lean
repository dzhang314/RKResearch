module

public import RKCert.ReviewedNative.DualSupport12
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! The absolute three remaining ordinary clock test after the five
opening rows are paid. Only three weighted moments and literal pair
equality are needed, not an interpolated degree-eight global profile. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Late

open RKResearch Graded
open scoped Matrix BigOperators

variable {K : Type*} [Field K]

theorem three_weighted_probes
    (u d v a b c : K)
    (u0 : u≠0) (d0 : d≠0) (v0 : v≠0)
    (ud : u≠d) (uv : u≠v) (dv : d≠v)
    (e1 : a*u+b*d+c*v=0)
    (e2 : a*u^2+b*d^2+c*v^2=0)
    (e3 : a*u^3+b*d^3+c*v^3=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  have A : u*(u-d)*(u-v)*a=0 := by
    linear_combination e3-(d+v)*e2+d*v*e1
  have B : d*(d-u)*(d-v)*b=0 := by
    linear_combination e3-(u+v)*e2+u*v*e1
  have C : v*(v-u)*(v-d)*c=0 := by
    linear_combination e3-(u+d)*e2+u*d*e1
  refine ⟨(mul_eq_zero.mp A).resolve_left ?_,(mul_eq_zero.mp B).resolve_left ?_,
    (mul_eq_zero.mp C).resolve_left ?_⟩
  · exact mul_ne_zero (mul_ne_zero u0 (sub_ne_zero.mpr ud)) (sub_ne_zero.mpr uv)
  · exact mul_ne_zero (mul_ne_zero d0 (sub_ne_zero.mpr ud.symm)) (sub_ne_zero.mpr dv)
  · exact mul_ne_zero (mul_ne_zero v0 (sub_ne_zero.mpr uv.symm)) (sub_ne_zero.mpr dv.symm)

def late (i : Fin 5) : Fin 15 := Fin.natAdd 10 i

@[simp] theorem late0 : late 0=10 := by decide
@[simp] theorem late1 : late 1=11 := by decide
@[simp] theorem late2 : late 2=12 := by decide
@[simp] theorem late3 : late 3=13 := by decide
@[simp] theorem late4 : late 4=14 := by decide

theorem remaining_three_clocks (b y w : Fin 15 → K) (u d v : K)
    (hY : y 10=u ∧ y 11=d ∧ y 12=v ∧ y 13=d ∧ y 14=0)
    (b10 : b 10≠0) (b12 : b 12≠0) (bPair : b 11+b 13≠0)
    (u0 : u≠0) (d0 : d≠0) (v0 : v≠0) (ud : u≠d) (uv : u≠v) (dv : d≠v)
    (early : ∀ i : Fin 15, i.val<10 → b i*w i=0)
    (pair : w 11=w 13)
    (moments : ∀ k : Fin 3, (∑ i : Fin 15, (b i*w i)*y i^(k.val+1))=0) :
    w 10=0 ∧ w 11=0 ∧ w 12=0 ∧ w 13=0 := by
  obtain ⟨y10,y11,y12,y13,y14⟩ := hY
  have h (k : Fin 3) :
      (∑ i : Fin 15, (b i*w i)*y i^(k.val+1)) =
        (b 10*w 10)*u^(k.val+1)+((b 11+b 13)*w 11)*d^(k.val+1)+(b 12*w 12)*v^(k.val+1) := by
    rw [Fin.sum_univ_add (a:=10) (b:=5)]
    have early0 : (∑ j : Fin 10, (b (Fin.castAdd 5 j)*w (Fin.castAdd 5 j))*
        y (Fin.castAdd 5 j)^(k.val+1))=0 := by
      apply Finset.sum_eq_zero
      intro j _
      have q := early (Fin.castAdd 5 j) j.isLt
      rw [q,zero_mul]
    rw [early0,zero_add]
    change ∑ j : Fin 5, (b (late j)*w (late j))*y (late j)^(k.val+1) = _
    rw [Fin.sum_univ_five]
    simp only [late0,late1,late2,late3,late4,y10,y11,y12,y13,y14,←pair]
    ring
  have e (k : Fin 3) := (h k).symm.trans (moments k)
  obtain ⟨a0,p0,c0⟩ := three_weighted_probes u d v (b 10*w 10)
    ((b 11+b 13)*w 11) (b 12*w 12) u0 d0 v0 ud uv dv
      (by simpa using e 0) (by simpa using e 1) (by simpa using e 2)
  have p := (mul_eq_zero.mp p0).resolve_left bPair
  exact ⟨(mul_eq_zero.mp a0).resolve_left b10,p,(mul_eq_zero.mp c0).resolve_left b12,pair.symm.trans p⟩

theorem terminal_of_zero_output (b w : Fin 15 → K)
    (bT : b 14≠0) (other : ∀ i : Fin 15, i≠14 → b i*w i=0)
    (output : row b w=0) : w 14=0 := by
  rw [row_apply,dotProduct,Fin.sum_univ_castSucc] at output
  have e (i : Fin 14) : i.castSucc ≠ (14:Fin 15) := by
    intro h
    have eq := congrArg Fin.val h
    change i.val=14 at eq
    omega
  have s : ∑ i : Fin 14, b i.castSucc*w i.castSucc=0 :=
    Finset.sum_eq_zero fun i _ => other _ (e i)
  rw [s,zero_add] at output
  exact (mul_eq_zero.mp output).resolve_left bT

def physicalPair (s : K) (i : Fin 15) : K :=
  if i=13 then s else if i=11 then -s else 0

theorem physicalPair_read (s : K) (w : Fin 15 → K) :
    row (physicalPair s) w=s*(w 13-w 11) := by
  rw [row_apply,dotProduct]
  have e (i : Fin 15) : physicalPair s i*w i =
      (if i=13 then s*w i else 0)+(if i=11 then -s*w i else 0) := by
    by_cases p : i=13
    · subst i
      norm_num [physicalPair]
    · by_cases q : i=11 <;> simp [physicalPair,p,q]
  simp_rw [e]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem paired_read_equal (A : Matrix (Fin 15) (Fin 15) K) (s scale : K) (H z : Fin 15 → K)
    (hNZ : s≠0) (pair : z 11=z 13) (silent : row H z=0)
    (adj : mat A.transpose (physicalPair s)=scale • (physicalPair s)+H) :
    mat A z 11=mat A z 13 := by
  have dual : row (physicalPair s) (mat A z)=row (mat A.transpose (physicalPair s)) z := by
    rw [row_apply,row_apply,mat_apply,mat_apply,dotProduct_comm (A.transpose *ᵥ physicalPair s),
      Matrix.dotProduct_transpose_mulVec]
  rw [adj,physicalPair_read] at dual
  have eqL (u v : Fin 15 → K) :
      row (scale • u+v) z=scale*row u z+row v z := by simp
  rw [eqL,physicalPair_read, pair,sub_self,mul_zero,mul_zero,silent,add_zero] at dual
  exact (sub_eq_zero.mp ((mul_eq_zero.mp dual).resolve_left hNZ)).symm

theorem paired_primitive_equal (A : Matrix (Fin 15) (Fin 15) K) (s scale : K)
    (H : Fin 15 → K) (m : Nat) (hNZ : s≠0) (pair : nodes A 11=nodes A 13)
    (silent : row H ((nodes A)^m)=0)
    (adj : mat A.transpose (physicalPair s)=scale • (physicalPair s)+H) :
    DualSupport12.forward A m 11=DualSupport12.forward A m 13 := by
  have q : ((nodes A)^m) 11=((nodes A)^m) 13 := by simp only [Pi.pow_apply,pair]
  have e := paired_read_equal A s scale H ((nodes A)^m) hNZ q silent adj
  simp only [DualSupport12.forward,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply,pair,e]

variable [CharZero K]

theorem paid_reverse_to_forward_moment {A : Matrix (Fin 15) (Fin 15) K} {b : Fin 15 → K}
    (scalar : ∀ j<12, ((j+1:Nat):K)*row b ((nodes A)^j)=1)
    (j m : Nat) (paid : j+m+1<12)
    (quiet : row (DualSupport12.reverse A b j) ((nodes A)^m)=0) :
    row (DualSupport12.moment A b j) (DualSupport12.forward A m)=0 := by
  have subL (a b v : Fin 15 → K) : row (a-b) v=row a v-row b v := by simp
  have smulL (s : K) (v w : Fin 15 → K) : row (s • v) w=s*row v w := by simp
  have dual (a v : Fin 15 → K) : row a (mat A v)=row (mat A.transpose a) v := by
    rw [row_apply,row_apply,mat_apply,mat_apply,dotProduct_comm (A.transpose *ᵥ a),
      Matrix.dotProduct_transpose_mulVec]
  rw [DualSupport12.reverse,subL,smulL,←dual,sub_eq_zero] at quiet
  rw [DualSupport12.forward,map_sub,map_smul,smul_eq_mul]
  have g := DualSupport12.mixed_scalar A b scalar j m paid
  have k : ((j+1:Nat):K) *
      (((m+1:Nat):K) * row (DualSupport12.moment A b j) (mat A ((nodes A)^m)) -
        row (DualSupport12.moment A b j) ((nodes A)^(m+1))) = 0 := by
    rw [mul_sub,mul_left_comm ((j+1:Nat):K) ((m+1:Nat):K),quiet,g,sub_self]
  exact (mul_eq_zero.mp k).resolve_left (Nat.cast_ne_zero.mpr (by omega))

end RKResearch.Certified.DIRK12MidpointForward.Late

#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.three_weighted_probes
#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.remaining_three_clocks
#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.paired_primitive_equal
#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.paid_reverse_to_forward_moment
