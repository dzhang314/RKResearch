module
public import RKCert.ReviewedNative.RowAnnihilator
public import RKCert.ReviewedNative.GradedSeparation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # A paid coordinate is external to the actual ordinary midpoint

Subtracting the last equation of a constant Cauchy profile leaves the
same already-checked square Cauchy kernel, after scaling each coefficient.
No new recurrence, sign premise or distinct physical-node premise enters.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

noncomputable section
variable {ι K : Type*} [Fintype ι] [Field K]
variable {A : Matrix ι ι K} {b : ι → K} {p q : ℕ}

theorem paid_constant_cauchy (ho : HasOrder A b p) (pay : 2*q+1≤p)
    (a : Fin q→K) (c : K)
    (test : ∀ i : Fin (q+1), (∑ j : Fin q, a j/((i.val+j.val+2:ℕ):K))=c) :
    a=0 ∧ c=0 := by
  let z : Fin q→K := fun j => a j/((q+j.val+2:ℕ):K)
  have yn (j : Fin q) : ((q+j.val+2:ℕ):K)≠0 := by
    exact (ho.natCast_isUnit (by omega : 0<q+j.val+2) (by have := j.isLt; omega)).ne_zero
  have sq (i : Fin q) : (∑ j : Fin q, z j / ((i.val+j.val+2:ℕ):K)) = 0 := by
    have xn (j : Fin q) : ((i.val+j.val+2:ℕ):K)≠0 := by
      have hj : 0 < i.val+j.val+2 := by omega
      exact (ho.natCast_isUnit hj (by have :=i.isLt;have :=j.isLt;omega)).ne_zero
    have cp : 0 < q-i.val := by have := i.isLt; omega
    have cn : ((q-i.val:ℕ):K)≠0 :=
      (ho.natCast_isUnit cp (by omega)).ne_zero
    have diff :
        (∑ j : Fin q, (a j/((i.val+j.val+2:ℕ):K)-a j/((q+j.val+2:ℕ):K)))=0 := by
      rw [Finset.sum_sub_distrib]
      have e₀ := test i.castSucc
      have e₁ := test (Fin.last q)
      change (∑ j : Fin q,a j/((i.val+j.val+2:ℕ):K))=c at e₀
      change (∑ j : Fin q,a j/((q+j.val+2:ℕ):K))=c at e₁
      rw [e₀,e₁,sub_self]
    have scaled :
        ((q-i.val:ℕ):K)*(∑ j : Fin q,z j/((i.val+j.val+2:ℕ):K))=0 := by
      rw [←diff,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have e :
          ((q-i.val:ℕ):K)=((q+j.val+2:ℕ):K)-((i.val+j.val+2:ℕ):K) := by
        have iq : i.val ≤ q := Nat.le_of_lt i.isLt
        rw [Nat.cast_sub iq]
        simp only [Nat.cast_add]
        ring
      rw [e]
      change
        (((q+j.val+2:ℕ):K)-((i.val+j.val+2:ℕ):K))*
            ((a j/((q+j.val+2:ℕ):K))/((i.val+j.val+2:ℕ):K)) =
          a j/((i.val+j.val+2:ℕ):K)-a j/((q+j.val+2:ℕ):K)
      generalize ex : ((i.val+j.val+2:ℕ):K) = x
      generalize ey : ((q+j.val+2:ℕ):K) = y
      have hx : x ≠ 0 := ex ▸ xn j
      have hy : y ≠ 0 := ey ▸ yn j
      field_simp [hx,hy]
    exact (mul_eq_zero.mp scaled).resolve_left cn
  have zl := moments_detect ho (n:=q) (d:=2) (by decide) (by omega)
    (fun i j=>by have :=i.isLt;have :=j.isLt;omega) z sq
  have az : a=0 := by
    ext j
    change a j=0
    by_contra nz
    exact div_ne_zero nz (yn j) (zl j)
  exact ⟨az,by simpa [az] using (test (Fin.last q)).symm⟩

section Physical
variable {s : ℕ} {T : Matrix (Fin (s+1)) (Fin (s+1)) K} {w : Fin (s+1)→K}

/-- A real stage with nonzero weight and clock 1 is not itself a paid
column at the ordinary midpoint. Its single unit remains at that stage. -/
theorem endpoint_coordinate_out (ha : ∀ i j,i≤j → T i j=0)
    (ho : HasOrder T w p) (pay : 2*q+1≤p) (t : Fin (s+1))
    (live : w t≠0) (atOne : nodes T t=1) :
    coordinate (K:=K) t ∉ treeSpace T q := by
  classical
  intro ht
  have c0 : nodes T 0=0 := by
    simp only [nodes,Matrix.mulVec,dotProduct]
    exact Finset.sum_eq_zero (fun i _=>by rw [ha 0 i (Fin.zero_le i),zero_mul])
  have nt : (0:Fin (s+1))≠t := by
    intro e
    exact zero_ne_one (c0.symm.trans (e.symm ▸ atOne))
  have e0 : coordinate (K:=K) t 0=0 := by simp [coordinate,nt]
  rw [treeSpace_coeff_sup ho (by omega)] at ht
  obtain ⟨v,hv,f,hf,e⟩ := Submodule.mem_sup.mp ht
  obtain ⟨a,rfl⟩:=hv
  have a0 : a 0=0 := by
    have h := congrFun e 0
    have f0 : f 0 = 0 := origin_zeroSpace ha q hf
    rw [Pi.add_apply,coeffEval_origin ha,f0,add_zero,e0] at h
    exact h
  have htest (i : Fin (q+1)) :
      (∑ j : Fin q, a j.succ/((i.val+j.val+2:ℕ):K))=w t := by
    have h := congrArg (probe T w i.val) e
    have wz : probe T w i.val f=0 := probe_zeroSpace ho (by have :=i.isLt;omega) hf
    have hc : probe T w i.val (coordinate t)=w t := by
      change row _ (coordinate t)=w t
      rw [row_coordinate,atOne,one_pow,mul_one]
    rw [map_add,wz,add_zero,probe_coeffEval ho (by have := i.isLt;omega),
      Fin.sum_univ_succ,a0,zero_div,zero_add,hc] at h
    simpa only [Fin.val_succ,Nat.add_assoc] using h
  exact live (paid_constant_cauchy ho pay (fun j : Fin q=>a j.succ) _ htest).2
end Physical
end
end RKResearch.Certified.Graded.Reverse
