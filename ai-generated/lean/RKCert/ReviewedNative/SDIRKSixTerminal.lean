module

public import RKCert.ReviewedNative.SDIRKSixReverse

@[expose] public section

/-! # Last two physical columns at strict SDIRK(6,6) saturation

No invertibility of diag(b) is assumed. Instead the saturated six-row census
sees every nonzero column and therefore forces the two terminal weights to be
nonzero and the two terminal nodes to be distinct.
-/

namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix
variable {K : Type*} [Field K] {s : ℕ}

/-- Standard coordinate column. -/
abbrev coord (j : Fin s) : (Fin s → K) := Pi.single j 1

theorem mat_coord (A : Matrix (Fin s) (Fin s) K) (j i : Fin s) : mat A (coord j) i = A i j := by
  simp [Matrix.mulVec, dotProduct, coord, Pi.single_apply, mul_ite]

theorem diag_coord (y : (Fin s → K)) (j : Fin s) : diag y (coord j) = y j • coord j := by
  ext i; by_cases h : i=j
  · subst i; simp [coord]
  · simp [coord,h]

theorem row_coord (b : (Fin s → K)) (j : Fin s) : row b (coord j) = b j := by
  simp [dotProduct, coord, Pi.single_apply, mul_ite]

theorem probe_coord (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) (k : ℕ) (j : Fin s) :
    probe A b k (coord j) = b j * nodes A j ^ k := row_coord _ _

variable {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)} {γ : K}

theorem mat_coord_five (ha : A.IsLowerTriangular) (hd : ∀i,A i i=γ) : mat A (coord 5)=γ • coord 5 := by
  ext i
  rw [mat_coord]
  by_cases hi : i=5
  · subst i; simp [coord,hd]
  · have hh : i<5 := by change i.val<5; have : i.val≠5 := fun h => hi (Fin.ext h); omega
    simp [@ha i 5 hh,coord,hi]

theorem mat_coord_four (ha : A.IsLowerTriangular) (hd : ∀i,A i i=γ) :
    mat A (coord 4)=γ • coord 4 + A 5 4 • coord 5 := by
  ext i
  rw [mat_coord]
  by_cases h4 : i=4
  · subst i; simp [coord,hd]
  by_cases h5 : i=5
  · subst i; simp [coord]
  · have hh : i<4 := by
      change i.val<4
      have : i.val≠4 := fun h => h4 (Fin.ext h)
      have : i.val≠5 := fun h => h5 (Fin.ext h)
      omega
    simp [@ha i 4 hh,coord,h4,h5]

theorem commutator_coord_five (ha : A.IsLowerTriangular) (hd : ∀i,A i i=γ) :
    volterra A (coord 5) = -(γ^2) • coord 5 := by
  change diag _ (mat A (coord 5)) - mat A (diag _ (coord 5)) - mat A (mat A (coord 5)) = _
  rw [mat_coord_five ha hd, diag_coord]
  simp only [map_smul, diag_coord,mat_coord_five ha hd,smul_smul]
  ext i; simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring

theorem commutator_coord_four (ha : A.IsLowerTriangular) (hd : ∀i,A i i=γ) :
    volterra A (coord 4) = -(γ^2) • coord 4 +
      ((nodes A 5-nodes A 4-2*γ)*A 5 4) • coord 5 := by
  change diag _ (mat A (coord 4)) - mat A (diag _ (coord 4)) - mat A (mat A (coord 4)) = _
  rw [mat_coord_four ha hd, diag_coord]
  simp only [map_smul, map_add, diag_coord,mat_coord_five ha hd,mat_coord_four ha hd,smul_smul]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring

/-- If a commutator eigenvector is invisible to all raw moment rows, it vanishes.
Only arithmetic consequences of the purchased order-six conditions are used. -/
theorem invisible_eigenvector_zero (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (hn : ∀i,A i i≠0) (v : (Fin 6 → K)) (r : K) (he : volterra A v = r • v)
    (hp : ∀ k, probe A b k v=0) : v=0 := by
  ext i
  obtain ⟨a,c,d,h⟩ := canonical_rows_span ho ha hn (LinearMap.proj i)
  have hi := h v
  change v i=0
  simpa only [he, map_smul, smul_eq_mul, hp, mul_zero, Finset.sum_const_zero, add_zero,
    LinearMap.proj_apply] using hi

/-- Concrete terminal incidence with the original unscaled nodes. -/
theorem order_six_terminal_chronology (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (hd : ∀i,A i i=γ) (hγ : γ≠0) :
    b 5≠0 ∧ b 4≠0 ∧ nodes A 5=1-γ ∧ nodes A 5≠nodes A 4 ∧
      b 5*A 5 4=(nodes A 5-nodes A 4)*b 4 := by
  have hn (i) : A i i≠0 := hd i ▸ hγ
  have h5 (hz : b 5=0) : False := by
    have h := invisible_eigenvector_zero ho ha hn (coord 5) (-(γ^2)) (commutator_coord_five ha hd)
      (fun k => by rw [probe_coord,hz,zero_mul])
    have h' := congrFun h 5; simp [coord] at h'
  have hD := order_six_D1 ho ha hn
  have h5' := LinearMap.congr_fun hD (coord 5)
  change row b (mat A (coord 5)) + row b (diag _ (coord 5)) - row b (coord 5) = 0 at h5'
  rw [mat_coord_five ha hd, diag_coord, map_smul, map_smul, row_coord, smul_eq_mul,
    smul_eq_mul] at h5'
  have hc5 : nodes A 5=1-γ := by
    have hh : (nodes A 5-(1-γ))*b 5=0 := by linear_combination h5'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right h5)
  have h4' := LinearMap.congr_fun hD (coord 4)
  change row b (mat A (coord 4)) + row b (diag _ (coord 4)) - row b (coord 4) = 0 at h4'
  rw [mat_coord_four ha hd,diag_coord,map_add,map_smul,map_smul,map_smul,
    row_coord,row_coord,smul_eq_mul,smul_eq_mul,smul_eq_mul] at h4'
  have hlink : b 5*A 5 4=(nodes A 5-nodes A 4)*b 4 := by rw [hc5]; linear_combination h4'
  have eq4 (ht : A 5 4=0) : volterra A (coord 4) = -(γ^2) • coord 4 := by
    simpa only [ht,mul_zero, zero_smul,add_zero] using commutator_coord_four ha hd
  have hb4 (hz:b 4=0) : False := by
    have h := hlink
    rw [hz, mul_zero] at h
    have ht := (mul_eq_zero.mp h).resolve_left h5
    have hh := invisible_eigenvector_zero ho ha hn (coord 4) (-(γ^2)) (eq4 ht)
      (fun k => by rw [probe_coord,hz,zero_mul])
    have h' := congrFun hh 4; simp [coord] at h'
  refine ⟨h5,hb4,hc5,?_,hlink⟩
  intro hc
  have h := hlink
  rw [hc,sub_self,zero_mul] at h
  have ht := (mul_eq_zero.mp h).resolve_left h5
  let v : (Fin 6 → K) := b 5 • coord 4-b 4 • coord 5
  have he : volterra A v=-(γ^2) • v := by
    dsimp [v]
    rw [map_sub,map_smul,map_smul,eq4 ht,commutator_coord_five ha hd,smul_sub]
    ext i; simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring
  have hp (k) : probe A b k v=0 := by
    dsimp [v]; rw [map_sub,map_smul,map_smul,probe_coord,probe_coord,hc]
    change _ * (_*_) - _ * (_*_) = (0:K)
    ring
  have hv := invisible_eigenvector_zero ho ha hn v _ he hp
  have hval := congrFun hv 4
  exact h5 (by simpa [v,coord] using hval)

end RKResearch.Certified.Graded.SDIRKSix
