module

public import RKCert.ReviewedNative.CausalStage
public import RKCert.ReviewedNative.ERK17ScalarPorts

@[expose] public section

/-! # From four measured clocks to the reviewed-native scalar obligation

The interface is on the original matrix, not a selected or reordered
tableau. Only distinct active *clock values* are counted, not the number
of indices that carry them. -/
namespace RKResearch.Certified.ERK17
open RKResearch.Certified.Graded RKCert.Endpoint Polynomial
open RKCert.ReviewedNative.ERK17.Scalar

variable {K : Type*} [Field K] {s : ℕ}
noncomputable section

/-- Chronological rows with a nonzero signed measurement. -/
def active (w : Fin s → K) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter (fun i => w i ≠ 0)

@[simp] theorem mem_active (w : Fin s → K) (i : Fin s) : i ∈ active w ↔ w i ≠ 0 := by
  classical
  simp [active]

/-- Distinct clocks of the active rows. -/
def sites (c w : Fin s → K) : Finset K := by
  classical
  exact (active w).image c

theorem mem_sites {c w : Fin s → K} {u : K} :
    u ∈ sites c w ↔ ∃ i, w i ≠ 0 ∧ c i = u := by
  classical
  simp only [sites,Finset.mem_image,mem_active]

/-- Geometric data at four distinct, signed measurement clocks.
No assumptions are made about the number of active rows, the original
output weights, or the unused value of the feeder at the final row. -/
structure PhysicalFourPort (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (w θ : Fin (s+1) → K) (P : K[X]) : Prop where
  degree : P.natDegree ≤ 5
  cardinal : (sites (nodes A) w).card = 4
  nonzeroAt : ∀ i, w i ≠ 0 → P.eval (nodes A i) ≠ 0
  inactive : ∀ i, w i = 0 → i ≠ Fin.last s → θ i = 0
  origin : w 0 = 0 → P.eval 0 = 0
  quadrature : ∀ R : K[X], R.natDegree ≤ 10 →
    (formalPrimitive (R*((1-X)*P))).eval 1 = ∑ i, R.eval (nodes A i)*w i
  primitive : ∀ R : K[X], R.natDegree ≤ 2 → ∀ i, w i ≠ 0 →
    mat A (fun j => R.eval (nodes A j)*θ j) i = (formalPrimitive (R*P)).eval (nodes A i)

variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {w θ : Fin (s+1) → K} {P : K[X]}

/-- Only active predecessor rows matter in a primitive probe.
The last row is never a predecessor. -/
theorem PhysicalFourPort.primitive_zero_of_prefix (B : PhysicalFourPort A w θ P)
    (ha : ∀ i j, i ≤ j → A i j = 0) {i : Fin (s+1)} (wi : w i ≠ 0)
    (R : K[X]) (deg : R.natDegree ≤ 2)
    (zero : ∀ j, j < i → w j ≠ 0 → R.eval (nodes A j) = 0) :
    (formalPrimitive (R*P)).eval (nodes A i) = 0 := by
  rw [←B.primitive R deg i wi]
  apply causal_mat ha i
  intro j hj
  change j < i at hj
  by_cases wj : w j = 0
  · rw [B.inactive j wj (fun eq => not_lt_of_ge (Fin.le_last i) (eq ▸ hj)),mul_zero]
  · rw [zero j hj wj,zero_mul]

/-- With the origin active, use the first nonzero physical measurement clock
and the three nonzero active clock values. The two payments are causal. -/
theorem PhysicalFourPort.mesh_of_origin [CharZero K] (B : PhysicalFourPort A w θ P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (origin : (0:K) ∈ sites (nodes A) w) :
    ∃ N : K[X], ∃ u : K, MeshPorts P N u := by
  classical
  let S := (sites (nodes A) w).erase 0
  have cs : S.card = 3 := by rw [Finset.card_erase_of_mem origin,B.cardinal]
  let D := (active w).filter (fun i => nodes A i ≠ 0)
  have nonempty : D.Nonempty := by
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    obtain ⟨x0,site⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,wj,cj⟩ := mem_sites.mp site
    exact ⟨j,Finset.mem_filter.mpr ⟨(mem_active w j).mpr wj,cj ▸ x0⟩⟩
  let i := D.min' nonempty
  have di := Finset.mem_filter.mp (D.min'_mem nonempty)
  have wi : w i ≠ 0 := (mem_active w i).mp di.1
  have hin : nodes A i ∈ S := Finset.mem_erase.mpr ⟨di.2,mem_sites.mpr ⟨i,wi,rfl⟩⟩
  have early (j : Fin (s+1)) (ji : j < i) (wj : w j ≠ 0) : nodes A j = 0 := by
    by_contra bad
    exact not_le_of_gt ji (D.min'_le _ (Finset.mem_filter.mpr ⟨(mem_active w j).mpr wj,bad⟩))
  have first := B.primitive_zero_of_prefix ha wi X (by simp)
    (fun j ji wj => by rw [eval_X,early j ji wj])
  have second := B.primitive_zero_of_prefix ha wi (X^2) (by rw [natDegree_X_pow])
    (fun j ji wj => by rw [eval_pow,eval_X,early j ji wj]; simp)
  refine ⟨nodalHull S,nodes A i,MeshPorts.of_quadrature
    ⟨di.2,B.nonzeroAt i wi,first,second⟩ B.degree (nodes A) w S cs.le hin ?_ B.quadrature⟩
  intro j wj
  by_cases zj : nodes A j = 0
  · exact Or.inl zj
  · exact Or.inr (Finset.mem_erase.mpr ⟨zj,mem_sites.mpr ⟨j,wj,rfl⟩⟩)

/-- Scalar endpoint statement for the case where the origin is absent.
It does not mention an array. Over an ordered field this gate is proved
by the existing 3+2 primitive obstruction. -/
def QuarticGate (K : Type*) [Field K] : Prop :=
  ∀ (Q : K[X]), Q.natDegree ≤ 4 → ∀ {u v : K}, u ≠ 0 → v ≠ 0 → v ≠ u →
    (∀ R : K[X], R.natDegree ≤ 2 → (formalPrimitive (R*(X*Q))).eval u = 0) →
    (∀ R : K[X], R.natDegree ≤ 1 → (formalPrimitive (R*(X*(X-C u)*Q))).eval v = 0) →
    Q = 0

/-- With no active origin, the earliest active clock gives three primitive
tests and the earliest different active clock gives two. -/
theorem PhysicalFourPort.no_origin_of_quartic (B : PhysicalFourPort A w θ P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (gate : QuarticGate K)
    (absent : (0:K) ∉ sites (nodes A) w) : False := by
  classical
  let c := nodes A
  let D := active w
  have nd : D.Nonempty := by
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by rw [B.cardinal]; decide : 0 < (sites c w).card)
    obtain ⟨i,wi,_⟩ := mem_sites.mp hu
    exact ⟨i,(mem_active w i).mpr wi⟩
  let i := D.min' nd
  let u := c i
  have wi : w i ≠ 0 := (mem_active w i).mp (D.min'_mem nd)
  have pn : P ≠ 0 := fun z => B.nonzeroAt i wi (by rw [z,eval_zero])
  have c0 : c 0 = 0 := by
    change (∑ j, A 0 j * (1 : Fin (s+1) → K) j) = 0
    apply Finset.sum_eq_zero
    intro j _
    rw [ha 0 j (Fin.zero_le j),zero_mul]
  have w0 : w 0 = 0 := by
    by_contra wn
    exact absent (mem_sites.mpr ⟨0,wn,c0⟩)
  have nz (j : Fin (s+1)) (wj : w j ≠ 0) : c j ≠ 0 :=
    fun z => absent (mem_sites.mpr ⟨j,wj,z⟩)
  have dvd : (X : K[X]) ∣ P := by
    rw [X_dvd_iff,coeff_zero_eq_eval_zero]
    exact B.origin w0
  obtain ⟨Q,hQ⟩ := dvd
  have qn : Q ≠ 0 := fun z => pn (by rw [hQ,z,mul_zero])
  have qd : Q.natDegree ≤ 4 := by
    have d := B.degree
    rw [hQ,natDegree_X_mul qn] at d
    omega
  let E := D.filter (fun j => c j ≠ u)
  have ne : E.Nonempty := by
    by_contra empty
    have sub : sites c w ⊆ {u} := by
      intro z hz
      obtain ⟨j,wj,rfl⟩ := mem_sites.mp hz
      by_contra fake
      exact empty ⟨j,Finset.mem_filter.mpr
        ⟨(mem_active w j).mpr wj,fun equal => fake (Finset.mem_singleton.mpr equal)⟩⟩
    have small := Finset.card_le_card sub
    rw [B.cardinal,Finset.card_singleton] at small
    omega
  let j := E.min' ne
  have ej := Finset.mem_filter.mp (E.min'_mem ne)
  have wj : w j ≠ 0 := (mem_active w j).mp ej.1
  apply qn (gate Q qd (nz i wi) (nz j wj) ej.2 ?_ ?_)
  · intro R deg
    rw [←hQ]
    apply B.primitive_zero_of_prefix ha wi R deg
    intro l li wl
    exact False.elim (not_le_of_gt li (D.min'_le _ ((mem_active w l).mpr wl)))
  · intro R deg
    let H := R*(X-C u)
    have hd : H.natDegree ≤ 2 := natDegree_mul_le.trans (by rw [natDegree_X_sub_C]; omega)
    have test := B.primitive_zero_of_prefix ha wj H hd (by
      intro l lj wl
      have eq : c l = u := by
        by_contra bad
        exact not_le_of_gt lj (E.min'_le _ (Finset.mem_filter.mpr ⟨(mem_active w l).mpr wl,bad⟩))
      change H.eval (c l) = 0
      simp [H,eq])
    rwa [show H*P=R*(X*(X-C u)*Q) by dsimp [H]; rw [hQ]; ring] at test

end
end RKResearch.Certified.ERK17
