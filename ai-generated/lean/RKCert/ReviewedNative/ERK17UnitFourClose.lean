module

public import RKCert.ReviewedNative.ERK17UnitFourPort
public import RKCert.ReviewedNative.ERK17ContrastCount
public import RKCert.ReviewedNative.NativeQuinticPorts

@[expose] public section

/-! # The exact scalar seam for the unmarked four-port

An active origin consumes the fixed Radau first-primitive gate. Otherwise
the true first two distinct active original clocks give all four and
three native primitive tests on the polynomial after its origin factor.
No order for any other matrix is needed. -/
namespace RKResearch.Certified.ERK17
open Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Hidden (activeRows mem_activeRows)
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {W θ : Fin (s+1)→K} {P : K[X]}

set_option maxRecDepth 3500 in
set_option maxHeartbeats 850000 in
theorem UnitPhysicalFourPort.impossible_of_origin (B : UnitPhysicalFourPort A W θ P)
    (ha : ∀ i j,i≤j → A i j=0) (gate : RadauFirstGate K)
    (origin : (0:K)∈weightedSites (nodes A) θ) : False := by
  let c := nodes A
  let S := weightedSites c θ
  let T := S.erase 0
  let N := nodalHull T
  have td : T.card=3 := by
    change (S.erase 0).card=3
    rw [Finset.card_erase_of_mem origin,show S.card=4 from B.sites]
  have nn : N≠0 := (monic_nodalHull T).ne_zero
  have nd : N.natDegree=3 := (natDegree_nodalHull T).trans td
  have root (a : K) (m : a∈T) : N.eval a=0 := nodalHull_eval_of_mem m
  have tests (k : Fin 8) : (RKResearch.Certified.Graded.primitive (X^k.val*(X*(P*N)))).eval 1=0 := by
    let R : K[X] := X^k.val*(X*N)
    have d : R.natDegree≤11 := by
      have e := natDegree_mul_le (p:=X^k.val) (q:=X*N)
      have f := natDegree_mul_le (p:=X) (q:=N)
      rw [natDegree_X_pow] at e
      rw [natDegree_X,nd] at f
      dsimp only [R]
      have hk := k.isLt
      omega
    have row : (∑ i,weightedEval c W R i)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases wz : W i=0
      · simp [wz]
      · by_cases c0 : c i=0
        · simp [R,c0]
        · have hit : c i∈T := Finset.mem_erase.mpr
            ⟨c0,mem_weightedSites.mpr ⟨i,(B.measured i wz).2,rfl⟩⟩
          simp [R,root _ hit]
    have e := B.quadrature R d
    rw [row,show R*P=X^k.val*(X*(P*N)) by dsimp [R];ring] at e
    exact e.symm
  let D := (activeRows θ).filter (fun i=>c i≠0)
  have ne : D.Nonempty := by
    obtain ⟨a,aT⟩ := Finset.card_pos.mp (by omega : 0<T.card)
    obtain ⟨a0,aS⟩ := Finset.mem_erase.mp aT
    obtain ⟨i,wi,hi⟩ := mem_weightedSites.mp aS
    exact ⟨i,Finset.mem_filter.mpr ⟨(mem_activeRows i).mpr wi,hi.symm ▸ a0⟩⟩
  let i := D.min' ne
  have h := Finset.mem_filter.mp (D.min'_mem ne)
  have wi : θ i≠0 := (mem_activeRows i).mp h.1
  have x0 : c i≠0 := h.2
  have hit : c i∈T := Finset.mem_erase.mpr ⟨x0,mem_weightedSites.mpr ⟨i,wi,rfl⟩⟩
  have first := B.primitive_zero_of_prefix ha wi X (by simp) (by
    intro j ji wj
    have v : c j=0 := by
      by_contra nz
      exact (not_le_of_gt ji) (D.min'_le _ (Finset.mem_filter.mpr ⟨(mem_activeRows j).mpr wj,nz⟩))
    change X.eval (c j)=0
    rw [eval_X,v])
  exact gate P N (c i) B.nonzero B.degree nn nd (root _ hit) x0 tests first

variable [LinearOrder K] [IsStrictOrderedRing K]

set_option maxRecDepth 3500 in
set_option maxHeartbeats 850000 in
theorem UnitPhysicalFourPort.impossible_without_origin (B : UnitPhysicalFourPort A W θ P)
    (ha : ∀ i j,i≤j → A i j=0) (none : (0:K)∉weightedSites (nodes A) θ) : False := by
  classical
  let c := nodes A
  let S := weightedSites c θ
  let D := activeRows θ
  have nz (i : Fin (s+1)) (wi : θ i≠0) : c i≠0 := fun z =>
    none (mem_weightedSites.mpr ⟨i,wi,z⟩)
  have w0 : θ 0=0 := by
    by_contra h
    exact nz 0 h (unit_origin_clock_zero ha)
  have P0 : P.coeff 0=0 := by rw [coeff_zero_eq_eval_zero]; exact B.initial w0
  obtain ⟨Q,eq⟩ := X_dvd_iff.mpr P0
  have qn : Q≠0 := fun z => B.nonzero (by rw [eq,z,mul_zero])
  have qd : Q.natDegree≤5 := by
    have d := B.degree
    rw [eq,natDegree_mul X_ne_zero qn,natDegree_X] at d
    omega
  have Ds : D.Nonempty := by
    obtain ⟨a,aS⟩ := Finset.card_pos.mp (show 0<S.card by rw [show S.card=4 from B.sites]; decide)
    obtain ⟨i,wi,_⟩ := mem_weightedSites.mp aS
    exact ⟨i,(mem_activeRows i).mpr wi⟩
  let i := D.min' Ds
  let u := c i
  have wi : θ i≠0 := (mem_activeRows i).mp (D.min'_mem Ds)
  let E := D.filter (fun i=>c i≠u)
  have Es : E.Nonempty := by
    by_contra h
    have all : S⊆{u} := by
      intro a aS
      obtain ⟨k,wk,rfl⟩ := mem_weightedSites.mp aS
      apply Finset.mem_singleton.mpr
      by_contra ne
      exact h ⟨k,Finset.mem_filter.mpr ⟨(mem_activeRows k).mpr wk,ne⟩⟩
    have e := Finset.card_le_card all
    rw [show S.card=4 from B.sites,Finset.card_singleton] at e
    omega
  let j := E.min' Es
  have js := Finset.mem_filter.mp (E.min'_mem Es)
  have wj : θ j≠0 := (mem_activeRows j).mp js.1
  apply qn (RKCert.ReviewedNative.Quintic.quintic_four_three Q qd (nz i wi) (nz j wj) js.2 ?_ ?_)
  · intro k
    have p := B.primitive_zero_of_prefix ha wi ((X:K[X])^k.val)
      (by rw [natDegree_X_pow]; have := k.isLt; omega)
      (fun l lt wl => False.elim ((not_le_of_gt lt) (D.min'_le _ ((mem_activeRows l).mpr wl))))
    rwa [eq,show (X:K[X])^k.val*(X*Q)=X^(k.val+1)*Q by rw [pow_succ,mul_assoc]] at p
  · intro k
    let R : K[X] := X^k.val*(X-C u)
    have d : R.natDegree≤3 := by
      have e := natDegree_mul_le (p:=X^k.val) (q:=X-C u)
      rw [natDegree_X_pow,natDegree_X_sub_C] at e
      dsimp only [R]
      have := k.isLt
      omega
    have p := B.primitive_zero_of_prefix ha wj R d (by
      intro l lt wl
      have e : c l=u := by
        by_contra ne
        exact (not_le_of_gt lt) (E.min'_le _ (Finset.mem_filter.mpr ⟨(mem_activeRows l).mpr wl,ne⟩))
      change R.eval (c l)=0
      simp [R,e])
    rwa [eq,show R*(X*Q)=X^(k.val+1)*((X-C u)*Q) by dsimp [R]; rw [pow_succ]; ring] at p

theorem UnitPhysicalFourPort.impossible_of_radau (B : UnitPhysicalFourPort A W θ P)
    (ha : ∀ i j,i≤j → A i j=0) (gate : RadauFirstGate K) : False := by
  by_cases origin : (0:K)∈weightedSites (nodes A) θ
  · exact B.impossible_of_origin ha gate origin
  · exact B.impossible_without_origin ha origin

end
end RKResearch.Certified.ERK17
