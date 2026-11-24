module
public import RKCert.NodalOrbitBudget
public import RKCert.ERKNodalDetectorBudget

@[expose] public section

/-! # Short actual reverse horizons have a mandatory support surplus.

The proof charges a smaller paid band before the ambient nodal hull. This
works whether or not the full complementary annihilator is invariant and
whether or not nodes support pairs of physical stages. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Endpoint Polynomial Module
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

theorem seed_clock_marked (ho:HasTreeOrderAtLeast A b p) (k:ℕ) (h:k+3≤p) :
    (diag (mirror A)^k) (backSeed2 A b)∈marked A p (k+2) := by
  induction k with
  | zero =>
    rw [pow_zero,one_apply_eq_self]
    change backSeed2 A b∈annih (treeSpace A (p-1-2))
    exact backSeed2_annih ho (by omega)
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact marked_clock (j:=k+2) (by omega) (ih (by omega))

theorem seed_clock_annih (ho:HasTreeOrderAtLeast A b p) (j k:ℕ) (h:j+k+3≤p) :
    (diag (mirror A)^k) (backSeed2 A b)∈annih (treeSpace A j) := by
  have g:=seed_clock_marked ho k (by omega)
  change _∈annih (treeSpace A (p-1-(k+2))) at g
  exact mem_annih.mpr fun v hv=>mem_annih.mp g v (treeSpace_mono A (by omega) hv)

theorem reverse_seed_moments (ho:HasTreeOrderAtLeast A b p) (k:ℕ) (h:k+3≤p) :
    (∑ i,(mirror A i)^k*backSeed2 A b i)=0 := by
  have m:=mem_annih.mp (seed_clock_annih ho 0 k (by omega)) (1:Vec K s)
    (stageWeight_mem_space A .leaf (by simp [Tree.order]))
  simpa only [row_apply,Pi.one_apply,mul_one,Clock.pow_diag_apply] using m

theorem seed_band_annih (ho:HasTreeOrderAtLeast A b p) (j k:ℕ) (pay:j+k+2≤p) :
    orbitBand (mirror A) (backSeed2 A b) k≤annih (treeSpace A j) := by
  rintro _ ⟨f,rfl⟩
  let E:=weightedEval (mirror A) (backSeed2 A b)
  change E (ofFn k f)∈_
  by_cases kz:k=0
  · subst k
    have hz:f=0:=funext (fun i=>Fin.elim0 i)
    simp [hz]
  let P:=ofFn k f
  change E P∈_
  rw [P.as_sum_range' k (ofFn_natDegree_lt (by omega) f),map_sum]
  apply (annih (treeSpace A j)).sum_mem
  intro q hq
  have eq:E (monomial q (P.coeff q)) =
      P.coeff q • ((diag (mirror A)^q) (backSeed2 A b)) := by
    ext i
    simp [E,eval_monomial,Clock.pow_diag_apply,smul_eq_mul,mul_assoc]
  rw [eq]
  exact (annih (treeSpace A j)).smul_mem _ (seed_clock_annih ho j q (by
    have h:=Finset.mem_range.mp hq
    omega))

variable [CharZero K]

/-- If the true complementary annihilator sits inside the hull of the
quadratic reverse seed, the genuinely paid first k seed powers and r
incoming Hermite dimensions can never be counted twice. The upper
site-budget hypothesis ensures all separate nodal masses are zero. -/
theorem short_reverse_hull_rank (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {j k r:ℕ}
    (paidSeed:j+k+3≤p) (paidPrimitive:j+2*r+1≤p)
    (enough:k≤(orbitSites (mirror A) (backSeed2 A b)).card)
    (momentBudget:(orbitSites (mirror A) (backSeed2 A b)).card+2≤p)
    (cover:annih (treeSpace A j)≤nodalOrbit (mirror A) (backSeed2 A b)) :
    k+r≤(orbitSites (mirror A) (backSeed2 A b)).card := by
  let y:=mirror A
  let d:=backSeed2 A b
  let V:=orbitBand y d k
  let W:=nodalOrbit y d
  have NV:V.map (transMat A)≤W:=by
    rintro _ ⟨v,hv,rfl⟩
    apply cover
    have h:=seed_band_annih ho (j+1) k (by omega) hv
    apply mem_annih.mpr
    intro x hx
    rw [row_flip_mat]
    exact mem_annih.mp h _ (mat_treeSpace A j hx)
  have budget:(orbitSites y d).card+2≤p:=momentBudget
  have rank:=incoming_actual_budget ha ho paidPrimitive V W (orbitBand_le y d k)
    (nodalOrbit_mask y d) (nodalOrbit_mass y d (fun q h=>reverse_seed_moments ho q (by omega))) NV cover
  rw [show finrank K V=k from orbitBand_rank y d k enough,
    show finrank K W=(orbitSites y d).card from nodalOrbit_rank y d] at rank
  exact rank

/-- Terminal-zero companion of the support count. The original
zero-column and reflected endpoint charges no extra dimension. -/
theorem short_reverse_hull_rank_terminal (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {j k r:ℕ}
    (paidSeed:j+k+3≤p) (paidPrimitive:j+2*r+1≤p)
    (t:Fin s) (y0:mirror A t=0) (col:∀i,A i t=0)
    (enough:k≤(orbitSites (mirror A) (backSeed2 A b)).card)
    (momentBudget:(orbitSites (mirror A) (backSeed2 A b)).card+2≤p)
    (cover:(annih (treeSpace A j)⊓LinearMap.ker (LinearMap.proj t))≤
      nodalOrbit (mirror A) (backSeed2 A b)) :
    k+r≤(orbitSites (mirror A) (backSeed2 A b)).card := by
  let y:=mirror A
  let d:=backSeed2 A b
  let V:=orbitBand y d k
  let W:=nodalOrbit y d
  have NV:V.map (transMat A)≤W:=by
    rintro _ ⟨v,hv,rfl⟩
    apply cover
    have h:=seed_band_annih ho (j+1) k (by omega) hv
    refine ⟨mem_annih.mpr ?_,transMat_zero_column t col v⟩
    intro x hx
    rw [row_flip_mat]
    exact mem_annih.mp h _ (mat_treeSpace A j hx)
  have budget:(orbitSites y d).card+2≤p:=momentBudget
  have rank:=incoming_actual_budget_terminal ha ho paidPrimitive t y0 col V W (orbitBand_le y d k)
    (nodalOrbit_mask y d) (nodalOrbit_mass y d (fun q h=>reverse_seed_moments ho q (by omega))) NV cover
  rw [show finrank K V=k from orbitBand_rank y d k enough,
    show finrank K W=(orbitSites y d).card from nodalOrbit_rank y d] at rank
  exact rank

/-- The true weak-horizon order-sixteen L7 = dP5(Y) chart has at least
eight numerical quadratic-defect sites, without a real order or a sign
assumption on the output weights. -/
theorem order16_thin_reverse_eight_sites (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 16)
    (thin:annih (treeSpace A 8)=orbitBand (mirror A) (backSeed2 A b) 6) :
    8≤(orbitSites (mirror A) (backSeed2 A b)).card := by
  by_contra! c
  have cover:=thin.le.trans (orbitBand_le (mirror A) (backSeed2 A b) 6)
  have dims:=Submodule.finrank_mono ((back_annih ho 8 6 (by decide)).trans cover)
  have growth:=back_finrank ha ho 6 (by decide)
  rw [nodalOrbit_rank] at dims
  have h:=short_reverse_hull_rank ha ho (j:=8) (k:=5) (r:=3) (by decide) (by decide)
    (by omega) (by omega) cover
  omega

/-- In particular the seven-double support chart cannot occur. -/
theorem order16_no_seven_reverse_sites (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 16)
    (thin:annih (treeSpace A 8)=orbitBand (mirror A) (backSeed2 A b) 6)
    (seven:(orbitSites (mirror A) (backSeed2 A b)).card=7) : False := by
  have h:=order16_thin_reverse_eight_sites ha ho thin
  omega

end
end RKCert.Paired.ReverseHull
