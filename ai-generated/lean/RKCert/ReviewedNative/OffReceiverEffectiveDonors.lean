module

public import RKCert.ReviewedNative.EffectiveDonorClocks
import RKCert.ReviewedNative.TwoEndpointClockSeparation
import RKCert.NodalPrimitive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Effective donor cover with the normalized receiver clock removed -/
namespace RKResearch.Certified.Graded.EffectiveDonors

open RKResearch Polynomial RKCert.Endpoint
open scoped BigOperators Classical
noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]

/-- A positive shift excludes zero; all shifts exclude the entire receiver
clock, and aggregation is signed on original clock fibres. -/
def offReceiverSites (c w : ι→K) (x : K) (e : ℕ) : Finset K :=
  (Finset.univ.image c).filter fun y=>y≠x ∧ y^e≠0 ∧ clockMass c w y≠0

theorem mem_offReceiverSites {c w : ι→K} {x y : K} {e : ℕ} :
    y∈offReceiverSites c w x e ↔ (∃ i,c i=y) ∧ y≠x ∧ y^e≠0 ∧ clockMass c w y≠0 := by
  simp [offReceiverSites,Finset.mem_image]

private theorem sum_from_masses (c w : ι→K) (f : K→K) :
    (∑ i,w i*f (c i))=∑ x∈Finset.univ.image c,clockMass c w x*f x := by
  classical
  let S : Finset K := Finset.univ.image c
  calc
    _ = ∑ i : ι, ∑ x∈S, if c i=x then w i*f x else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have mem : c i∈S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rw [Finset.sum_eq_single (c i)]
      · simp
      · intro x _ off
        simp [Ne.symm off]
      · intro off
        exact (off mem).elim
    _ = ∑ x∈S, ∑ i : ι, if c i=x then w i*f x else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [clockMass,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases atX : c i=x <;> simp [atX]

/-- The coefficient-sum Cauchy step at arbitrary positive shift. This is
the elimination used by native paid_sum_cauchy, with shift explicit. -/
private theorem paid_sum_shift {A : Matrix ι ι K} {b : ι→K} {q n d : ℕ}
    (ho : HasOrder q A b) (positive : 0<d) (pay : 2*n+d≤q+1)
    (a : Fin (n+1)→K) (total : (∑ j,a j)=0)
    (tests : ∀ i : Fin n,(∑ j : Fin (n+1),a j/((i.val+j.val+d:ℕ):K))=0) :
    a=0 := by
  let w : Fin n→K := fun j=>((n:K)-(j.val:K))*a j.castSucc
  have nz (k : ℕ) (kp : 0<k) (kq : k≤q) : (k:K)≠0 :=
    (ho.natCast_isUnit kp kq).ne_zero
  have kernel (i : Fin n) : (∑ j : Fin n,w j/((i.val+j.val+d:ℕ):K))=0 := by
    let D : K := ((i.val+n+d:ℕ):K)
    have dn : D≠0 := nz _ (by omega) (by have hi:=i.isLt; omega)
    have t := tests i
    rw [Fin.sum_univ_castSucc] at t
    change (∑ j : Fin n,a j.castSucc/((i.val+j.val+d:ℕ):K))+
      a (Fin.last n)/D=0 at t
    have u := congrArg (fun x : K=>D*x) t
    have last : D*(a (Fin.last n)/D)=a (Fin.last n) := by field_simp
    rw [mul_zero,mul_add,Finset.mul_sum,last] at u
    have s := total
    rw [Fin.sum_univ_castSucc] at s
    have term (j : Fin n) : w j/((i.val+j.val+d:ℕ):K)=
        D*(a j.castSucc/((i.val+j.val+d:ℕ):K))-a j.castSucc := by
      have jn : ((i.val+j.val+d:ℕ):K)≠0 :=
        nz _ (by omega) (by have hi:=i.isLt; have hj:=j.isLt; omega)
      have diff : (n:K)-(j.val:K)=D-((i.val+j.val+d:ℕ):K) := by
        dsimp only [D]
        push_cast
        ring
      dsimp only [w]
      rw [diff]
      field_simp
    rw [Finset.sum_congr rfl (fun j _=>term j),Finset.sum_sub_distrib]
    linear_combination u-s
  have z := moments_detect ho (n:=n) (d:=d) positive (by omega)
    (fun i j=>by have hi:=i.isLt; have hj:=j.isLt; omega) w kernel
  have rest (j : Fin n) : a j.castSucc=0 := by
    have nn : (n:K)-(j.val:K)≠0 := by
      rw [←Nat.cast_sub (le_of_lt j.isLt)]
      exact nz _ (by have hj:=j.isLt; omega) (by omega)
    exact (mul_eq_zero.mp (z j)).resolve_left nn
  have last : a (Fin.last n)=0 := by
    rw [Fin.sum_univ_castSucc] at total
    simpa only [rest,Finset.sum_const_zero,zero_add] using total
  ext j
  exact Fin.lastCases last rest j

omit [Fintype ι] in
private theorem primitive_coeffs {P : K[X]} {n : ℕ} (pd : P.natDegree<n) (k : ℕ) :
    (primitive (X^k*P)).eval 1=∑ j : Fin n,P.coeff j.val/((k+j.val+1:ℕ):K) := by
  conv_lhs => rw [P.as_sum_range' n pd]
  rw [Finset.mul_sum,map_sum,eval_finsetSum,
    Fin.sum_univ_eq_sum_range (fun j=>P.coeff j/((k+j+1:ℕ):K)) n]
  apply Finset.sum_congr rfl
  intro j _
  simp only [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one,
    Nat.cast_add,Nat.cast_one]
  ring

/-- A cover of the effective clocks other than one, removing zero as
well if the shift is positive, pays the displayed lower bound. -/
theorem off_one_cover_card_of_hasOrder {A : Matrix ι ι K} {b : ι→K} {q n e : ℕ}
    (ho : HasOrder q A b) (budget : 2*n+e≤q) (D : Finset K)
    (covers : ∀ y,(∃ i,nodes A i=y) → y≠1 → y^e≠0 →
      y∉D → clockMass (nodes A) b y=0) :
    n≤D.card := by
  classical
  by_contra no
  let N := nodalHull D
  let P : K[X] := (1-X)*N
  have nd : N.natDegree<n := (natDegree_nodalHull D).trans_lt (lt_of_not_ge no)
  have oneDeg : (1-(X:K[X])).natDegree≤1 := natDegree_sub_le_of_le (p := (1 : K[X])) (q := X) (by rw [natDegree_one]) (natDegree_X (R:=K)).le
  have pd : P.natDegree≤n := by
    dsimp only [P]
    exact (natDegree_mul_le (p:=(1-X:K[X])) (q:=N)).trans (by omega)
  have oneNe : (1-(X:K[X]))≠0 := by
    intro z
    have h := congrArg (Polynomial.eval (0:K)) z
    simp at h
  have pn : P≠0 := mul_ne_zero oneNe (monic_nodalHull D).ne_zero
  have zeroProbe (k : ℕ) : probe A b (k+e) (evalNodes A P)=0 := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,mul_assoc]
    rw [sum_from_masses (nodes A) b (fun y=>y^(k+e)*P.eval y)]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases y1 : y=1
    · simp [y1,P]
    by_cases yp : y^e=0
    · simp [pow_add,yp]
    by_cases yd : y∈D
    · have root : N.eval y=0 := nodalHull_eval_of_mem yd
      simp [P,root]
    · obtain ⟨i,_,cy⟩ := Finset.mem_image.mp hy
      rw [covers y ⟨i,cy⟩ y1 yp yd,zero_mul]
  have atOne : P.eval 1=0 := by simp [P]
  have total : (∑ j : Fin (n+1),P.coeff j.val)=0 := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le pd)] at atOne
    rw [Fin.sum_univ_eq_sum_range (fun j=>P.coeff j) (n+1)]
    simpa only [one_pow,mul_one,one_mul] using atOne
  have tests (k : Fin n) :
      (∑ j : Fin (n+1),P.coeff j.val/((k.val+j.val+(e+1):ℕ):K))=0 := by
    have kp := k.isLt
    have pay := probe_evalNodes ho P (k.val+e) (by omega)
    rw [zeroProbe k.val,primitive_coeffs (Nat.lt_succ_of_le pd) (k.val+e)] at pay
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using pay.symm
  have coeffs := paid_sum_shift ho (n:=n) (d:=e+1) (by omega) (by omega) _ total tests
  apply pn
  ext j
  rw [coeff_zero]
  by_cases hj : j<n+1
  · exact congrFun coeffs (⟨j,hj⟩ : Fin (n+1))
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Deleting an original last coordinate at the excluded receiver clock
does not change any of the counted signed aggregates. -/
theorem offReceiverSites_remove_last {n : ℕ} (c w : Fin (n+1)→K) {x : K}
    (last : c (Fin.last n)=x) (e : ℕ) :
    offReceiverSites c w x e =
      offReceiverSites (fun i : Fin n=>c i.castSucc) (fun i : Fin n=>w i.castSucc) x e := by
  classical
  ext y
  by_cases hy : y=x
  · simp [mem_offReceiverSites,hy]
  have occ : (∃ i,c i=y) ↔ ∃ i : Fin n,c i.castSucc=y := by
    constructor
    · rintro ⟨i,hi⟩
      by_cases li : i=Fin.last n
      · rw [li,last] at hi
        exact (hy hi.symm).elim
      · have vne : i.val≠n := fun h=>li (Fin.ext h)
        have lt : i.val<n := by have h := i.isLt; omega
        let j : Fin n := ⟨i.val,lt⟩
        have cast : j.castSucc=i := Fin.ext rfl
        exact ⟨j,by rw [cast]; exact hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨i.castSucc,hi⟩
  have mass : clockMass c w y =
      clockMass (fun i : Fin n=>c i.castSucc) (fun i : Fin n=>w i.castSucc) y := by
    simp only [clockMass]
    rw [Fin.sum_univ_castSucc,last,if_neg (Ne.symm hy),add_zero]
  simp only [mem_offReceiverSites,occ,mass]

end
end RKResearch.Certified.Graded.EffectiveDonors
