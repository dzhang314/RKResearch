module

public import RKCert.DirkGradeSix
public import RKCert.ReceiverPrefix

@[expose] public section

/-! # Exact reverse budgets and physical terminal restriction

The spaces here are defined as annihilators of the ACTUAL ordinary tree
spans, not as an unverified algebra of marked rows. The paid action of an
ordinary column is pointwise multiplication. No product between two reverse
rows or order assumption on a deleted tableau is made. -/

namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p j k : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

theorem finrank_annih_eq (U : Submodule K (Vec K s)) :
    finrank K U + finrank K (annih U) = s := by
  have equiv : rowL (K:=K) (s:=s) = (dotProductEquiv K (Fin s)).toLinearMap := by
    ext u v
    rfl
  rw [annih,equiv,Submodule.comap_equiv_eq_map_symm,LinearEquiv.finrank_map_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq,Module.finrank_fin_fun]

theorem annih_antitone_paired : Antitone (annih (K:=K) (s:=s)) := by
  intro U V h w hw
  exact mem_annih.mpr (fun u hu => mem_annih.mp hw u (h hu))

theorem annih_annih_paired (U : Submodule K (Vec K s)) : annih (annih U)=U := by
  symm
  have hle : U ≤ annih (annih U) := annih_flip_le le_rfl
  have hd := finrank_annih_eq U
  have he := finrank_annih_eq (annih U)
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

theorem row_single_right (u : Vec K s) (i : Fin s) : row u (Pi.single i (1:K))=u i := by
  classical
  simp [row_apply,Pi.single_apply]

theorem row_single_left (u : Vec K s) (i : Fin s) : row (Pi.single i (1:K)) u=u i := by
  classical
  simp [row_apply,Pi.single_apply]

/-- All reverse rows available by ordinary-tree annihilation at complementary
grade. The submodule may be larger than a specified set of marked words. -/
def marked (A : Fin s → Fin s → K) (p j : ℕ) : Submodule K (Vec K s) :=
  annih (treeSpace A (p-1-j))

theorem marked_mono (A : Fin s → Fin s → K) (p : ℕ) : Monotone (marked A p) :=
  fun _ _ hj => annih_antitone_paired (treeSpace_mono A (by omega))

theorem marked_rank (A : Fin s → Fin s → K) (p j : ℕ) :
    finrank K (treeSpace A (p-1-j))+finrank K (marked A p j)=s :=
  finrank_annih_eq _

theorem marked_strict (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hl : 2 ≤ j) (hj : j+2 ≤ p) : marked A p j < marked A p (j+1) := by
  have ht := dirk_treeSpace_lt_succ ha ho (j:=p-1-(j+1)) (by omega)
  have hg := Submodule.finrank_lt_finrank_of_lt ht
  rw [show p-1-(j+1)+1=p-1-j by omega] at hg
  have h₀ := marked_rank A p j
  have h₁ := marked_rank A p (j+1)
  apply lt_of_le_of_ne (marked_mono A p (Nat.le_succ j))
  intro h
  have he := congrArg (fun T : Submodule K (Vec K s) => finrank K T) h
  change finrank K (marked A p j) = finrank K (marked A p (j+1)) at he
  omega

theorem marked_mat (hpay : j+2 ≤ p) {w : Vec K s} (hw : w∈marked A p j) :
    transMat A w∈marked A p (j+1) := by
  apply mem_annih.mpr
  intro v hv
  rw [row_flip_mat]
  exact mem_annih.mp hw _ (treeSpace_mono A (by omega) (mat_treeSpace A _ hv))

theorem marked_clock (hpay : j+2 ≤ p) {w : Vec K s} (hw : w∈marked A p j) :
    diag (mirror A) w∈marked A p (j+1) := by
  apply mem_annih.mpr
  intro v hv
  rw [row_flip_diag]
  exact mem_annih.mp hw _ (treeSpace_mono A (by omega) (mirror_treeSpace A _ hv))

/-- Pairing the reverse row times a genuine ordinary tree feature pays its
entire grade, without multiplying two reverse rows. -/
theorem marked_mul_tree (hpay : j+k+1 ≤ p) {w v : Vec K s}
    (hw : w∈marked A p j) (hv : v∈treeSpace A k) :
    w*v∈marked A p (j+k) := by
  apply mem_annih.mpr
  intro u hu
  rw [show row (w*v) u=row w (v*u) by
    simp only [row_apply,Pi.mul_apply, mul_assoc]]
  exact mem_annih.mp hw _ (treeSpace_mono A (by omega) (treeSpace_mul hv hu))

/-- The weight times an ordinary defect is a genuine paid reverse defect,
even at a zero output weight. -/
theorem weights_mul_zeroSpace (ho : HasTreeOrderAtLeast A b p) (hj : j+1≤p)
    {v : Vec K s} (hv : v∈zeroSpace A j) : b*v∈marked A p j := by
  apply mem_annih.mpr
  intro u hu
  rw [show row (b*v) u=probe A b 0 (v*u) by
    simp only [row_apply,Pi.mul_apply,probe,pow_zero,mul_one,mul_assoc]]
  apply probe_zeroSpace ho (by omega : 0+(j+(p-1-j))+1≤p)
  exact zeroSpace_mul_treeSpace ho (by omega) hv hu

theorem seed1_marked (ho : HasTreeOrderAtLeast A b p) (hp : 2≤p) :
    backSeed1 A b∈marked A p 1 := backSeed1_annih ho (by omega : (p-1-1)+2≤p)

theorem seed2_marked (ho : HasTreeOrderAtLeast A b p) (hp : 3≤p) :
    q₂ (transMat A) (mirror A) b∈marked A p 2 :=
  backSeed2_annih ho (by omega : (p-1-2)+3≤p)

theorem seed3_marked (ho : HasTreeOrderAtLeast A b p) (hp : 4≤p) :
    q₃ (transMat A) (mirror A) b∈marked A p 3 := by
  rw [back_seed3,marked,mem_annih]
  exact reflected_treeSpace ho _ 2 (by decide) (by omega)

theorem back_sub_marked (ho : HasTreeOrderAtLeast A b p) (hj : 2≤j) (hp : j+1≤p) :
    dirkBack A b (j-2)≤marked A p j :=
  dirkBack_annih ho _ _ (by omega)

theorem leaf_marked_zero {w : Vec K s} (hw : w∈marked A p j) : row w 1=0 :=
  mem_annih.mp hw 1 (stageWeight_mem_space A .leaf (by simp [Tree.order]))

/-- No tableau trim is paid for without verifying the actual rooted-tree
weights on the original lower triangle. -/
theorem order_on_lower_prefix (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    {t : ℕ} (ht : t≤s) (hw : ∀ i : Fin s, t ≤ i.val → b i=0) :
    HasTreeOrderAtLeast (prefixTableau A ht) (fun i => b (Fin.castLE ht i)) p := by
  have hc (v : Vec K s) : mat (prefixTableau A ht) (restrictCol (Fin.castLE ht) v) =
      restrictCol (Fin.castLE ht) (mat A v) := by
    ext i
    exact sum_on_prefix ht (fun j => A (Fin.castLE ht i) j * v j)
      (fun j hj => by rw [ha _ _ (by exact lt_of_lt_of_le i.isLt hj),zero_mul])
  have he (tree : Tree) : restrictCol (Fin.castLE ht) (stageWeight A tree) =
      stageWeight (prefixTableau A ht) tree :=
    restrict_stageWeight A _ _ tree.order (fun v _ => hc v) tree (by omega)
  intro tree htree
  have eq : weight (prefixTableau A ht) (fun i => b (Fin.castLE ht i)) tree =
      weight A b tree := by
    rw [weight,weight,←he]
    exact sum_on_prefix ht (fun i => b i*stageWeight A tree i)
      (fun i h => by rw [hw i h,zero_mul])
  rw [eq]
  exact ho tree htree

theorem lower_prefix (ha : LowerArray A) {t : ℕ} (ht : t≤s) :
    LowerArray (prefixTableau A ht) :=
  fun i j hij => ha (Fin.castLE ht i) (Fin.castLE ht j) hij

end RKCert.Paired
