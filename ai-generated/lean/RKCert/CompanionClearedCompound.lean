module

public import RKCert.CompanionExteriorEntries

@[expose] public section

/-! # Denominator-free ordered companion minors

Only the last original companion column is multiplied by the leading
coefficient. Thus each ordered minor clears at most one factor, even
when the underlying polynomial has repeated roots. -/
namespace RKCert.Compound
open Polynomial Set Set.powersetCard
open scoped Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Raw column of the companion resolvent. All nonlast columns are monic
variable minus the fixed subdiagonal. -/
def rawResolvent {n : ℕ} (b : Fin (n+1)→R) : Matrix (Fin n) (Fin n) R[X] :=
  fun i j =>
    if j.val+1<n then (if i=j then X else 0)-(if i.val=j.val+1 then 1 else 0)
    else (if i=j then C (b (Fin.last n))*X else 0)+C (b i.castSucc)

def rawMinor {n k : ℕ} (b : Fin (n+1)→R)
    (i j : powersetCard (Fin n) k) : R[X] :=
  (Matrix.submatrix (rawResolvent b) (powersetCard.ofFinEmbEquiv.symm i)
    (powersetCard.ofFinEmbEquiv.symm j)).det

/-- Membership expressed through the native ordered-subset embedding. -/
def hasLast {n k : ℕ} (j : powersetCard (Fin n) k) : Prop :=
  ∃ t : Fin k, ¬ (powersetCard.ofFinEmbEquiv.symm j t).val+1<n

theorem rawResolvent_map {n : ℕ} (f : R→+*S) (b : Fin (n+1)→R) :
    (mapRingHom f).mapMatrix (rawResolvent b) = rawResolvent (f ∘ b) := by
  apply Matrix.ext
  intro i j
  classical
  change (rawResolvent b i j).map f=_
  simp only [rawResolvent, Function.comp_apply]
  by_cases h : j.val+1<n <;> by_cases g : i=j <;> by_cases e : i.val=j.val+1 <;>
    simp [h,g,e,Polynomial.map_mul,Polynomial.map_C]

theorem rawMinor_map {n k : ℕ} (f : R→+*S) (b : Fin (n+1)→R)
    (i j : powersetCard (Fin n) k) :
    (rawMinor b i j).map f=rawMinor (f ∘ b) i j := by
  change (mapRingHom f) (rawMinor b i j)=_
  unfold rawMinor
  rw [(mapRingHom f).map_det_submatrix]
  have w := rawResolvent_map f b
  exact congrArg (fun M : Matrix (Fin n) (Fin n) S[X] =>
    (M.submatrix (powersetCard.ofFinEmbEquiv.symm i)
     (powersetCard.ofFinEmbEquiv.symm j)).det) w

theorem rawResolvent_outer_cap {n : ℕ} (b : Fin (n+1)→R) (i j : Fin n) :
    (rawResolvent b i j).natDegree≤1 := by
  classical
  unfold rawResolvent
  split_ifs
  · exact (natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp))
  · exact (natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp))
  · exact (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  · exact (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  · exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  · exact (natDegree_add_le _ _).trans (max_le (by simp) (by simp))

theorem rawMinor_outer_cap {n k : ℕ} (b : Fin (n+1)→R)
    (i j : powersetCard (Fin n) k) : (rawMinor b i j).natDegree≤k := by
  classical
  unfold rawMinor
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le Finset.univ _).trans
  apply (Finset.sum_le_sum (g:=fun _=>1) (fun x _ => rawResolvent_outer_cap b _ _)).trans
  simp

variable {K : Type*} [Field K]

/-- Evaluate one symbolic raw resolvent column. The vector b may be the
evaluated coefficients of an arbitrary nonmonic polynomial. -/
theorem rawResolvent_eval (q : K[X]) (b : Fin (q.natDegree+1)→K)
    (z : K) (v : Fin q.natDegree) (f : Fin q.natDegree)
    (below : ∀ i : Fin q.natDegree,b i.castSucc=b (Fin.last q.natDegree)*q.coeff i.val) :
    (rawResolvent b f v).eval z =
      (if v.val+1<q.natDegree then 1 else b (Fin.last q.natDegree)) *
        (Matrix.scalar (Fin q.natDegree) z-coefficientCompanion q) f v := by
  classical
  let n := q.natDegree
  by_cases h : v.val+1<n
  · by_cases e : f=v <;> by_cases l : f.val=v.val+1 <;>
      simp [rawResolvent,coefficientCompanion,Matrix.scalar,Matrix.diagonal,Matrix.sub_apply,h,e,l,n] at *
  · by_cases e : f=v
    · simp [rawResolvent,coefficientCompanion,Matrix.scalar,Matrix.diagonal,Matrix.sub_apply,h,e,n,
        below,mul_add]
    · simp [rawResolvent,coefficientCompanion,Matrix.scalar,Matrix.diagonal,Matrix.sub_apply,h,e,n,below]

theorem unique_last {n k : ℕ} (j : powersetCard (Fin n) k)
    {t s : Fin k} (ht : ¬(powersetCard.ofFinEmbEquiv.symm j t).val+1<n)
    (hs : ¬(powersetCard.ofFinEmbEquiv.symm j s).val+1<n) : t=s := by
  let m := powersetCard.ofFinEmbEquiv.symm j
  apply m.injective
  apply Fin.ext
  change ¬(m t).val+1<n at ht
  change ¬(m s).val+1<n at hs
  have x := (m t).isLt
  have y := (m s).isLt
  omega

theorem rawMinor_eval (q : K[X]) (b : Fin (q.natDegree+1)→K)
    (below : ∀ i : Fin q.natDegree,b i.castSucc=b (Fin.last q.natDegree)*q.coeff i.val)
    (z : K) {k : ℕ} (i j : powersetCard (Fin q.natDegree) k) :
    (rawMinor b i j).eval z =
      (if hasLast j then b (Fin.last q.natDegree) else 1) *
        orderedCompound k (Matrix.scalar (Fin q.natDegree) z-coefficientCompanion q) i j := by
  classical
  let r := powersetCard.ofFinEmbEquiv.symm i
  let c := powersetCard.ofFinEmbEquiv.symm j
  let s : Fin k→K := fun t =>
    if (c t).val+1<q.natDegree then 1 else b (Fin.last q.natDegree)
  let M := (Matrix.scalar (Fin q.natDegree) z-coefficientCompanion q).submatrix r c
  have d : (∏ t,s t)=(if hasLast j then b (Fin.last q.natDegree) else 1) := by
    split_ifs with h
    · obtain ⟨t,nt⟩ := h
      rw [Finset.prod_eq_single t]
      · simp [s,c,nt]
      · intro y _ ne
        have ly : (c y).val+1<q.natDegree := by
          by_contra hy
          exact ne (unique_last j hy nt)
        simp [s,ly]
      · simp
    · apply Finset.prod_eq_one
      intro t _
      have l : (c t).val+1<q.natDegree := by
        by_contra ls
        exact h ⟨t,ls⟩
      simp [s,l]
  change (evalRingHom z) (rawMinor b i j)=_
  rw [rawMinor,(evalRingHom z).map_det_submatrix]
  have eq :
      ((rawResolvent b).map (evalRingHom z)).submatrix r c =
        Matrix.of (fun x y => s y * M x y) := by
    ext x y
    exact rawResolvent_eval q b z (c y) (r x) below
  change (((rawResolvent b).map (evalRingHom z)).submatrix r c).det=_
  rw [eq,Matrix.det_mul_row,d]
  rfl

end
end RKCert.Compound
