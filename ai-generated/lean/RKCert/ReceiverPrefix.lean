module

public import RKCert.StagePrimitives
public import RKCert.ChronologicalCompression
public import RKCert.UniformERK

@[expose] public section

/-! # Prefix restriction and exact nonzero receivers

A stage that is exact through grade five at a nonzero node already needs
at least six earlier explicit stages. The preceding tableau and its
incoming row really satisfy the order-five tree equations after rescaling.
-/
namespace RKCert.Paired
open Polynomial

variable {K : Type*} [Field K] {s : ℕ}

def scaleTableau (r : K) (A : Fin s → Fin s → K) (i j : Fin s) : K := r * A i j

theorem scale_strict {A : Fin s → Fin s → K} (ha : StrictLower A) (r : K) :
    StrictLower (scaleTableau r A) := by
  intro i j hij; simp [scaleTableau,ha i j hij]

theorem scale_nodes (r : K) (A : Fin s → Fin s → K) :
    nodes (scaleTableau r A) = r • nodes A := by
  ext i; simp [nodes,scaleTableau,Finset.mul_sum]

/-- Every rooted-tree column is homogeneous of its stage grade. -/
theorem stageWeight_scale (r : K) (A : Fin s → Fin s → K) (t : Tree) :
    stageWeight (scaleTableau r A) t = r^(t.order-1) • stageWeight A t := by
  induction t with
  | leaf => ext i; simp [Tree.order,stageWeight]
  | attach t u iht ihu =>
    ext i
    have ht := t.order_pos; have hu := u.order_pos
    simp only [stageWeight, ihu, iht,scaleTableau,Pi.smul_apply,smul_eq_mul,Tree.order]
    have hh : (∑ j, (r * A i j) * (r^(t.order-1) * stageWeight A t j)) =
        (r * r^(t.order-1)) * (∑ j, A i j * stageWeight A t j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hh,show t.order+u.order-1=1+(t.order-1)+(u.order-1) by omega,pow_add,pow_add,pow_one]
    ring

theorem normTree_scale (r : K) (A : Fin s → Fin s → K) (t : Tree) :
    normTree (scaleTableau r A) t = r^(t.order-1) • normTree A t := by
  rw [normTree,normTree,stageWeight_scale,smul_comm]

theorem scale_zeroSpace {r : K} (hr : r≠0) (A : Fin s → Fin s → K) (q : ℕ) :
    zeroSpace (scaleTableau r A) q = zeroSpace A q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,u,he,ht,rfl⟩
    rw [normTree_scale,normTree_scale,← he,← smul_sub]
    exact (zeroSpace A q).smul_mem _ (normDiff_mem A t u he ht)
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,u,he,ht,rfl⟩
    have h := (zeroSpace (scaleTableau r A) q).smul_mem ((r^(t.order-1))⁻¹)
      (normDiff_mem (scaleTableau r A) t u he ht)
    change normTree A t - normTree A u ∈ zeroSpace (scaleTableau r A) q
    simpa only [normTree_scale,← he,← smul_sub,smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ hr),one_smul] using h

theorem scale_separated {r : K} (hr : r≠0) {A : Fin s → Fin s → K} {q : ℕ}
    (hs : Separated A q) : Separated (scaleTableau r A) q := by
  intro P hP hmem
  have he : evalNodes (scaleTableau r A) P = evalNodes A (P.comp (C r * X)) := by
    ext i; simp [scale_nodes,Polynomial.eval_comp]
  rw [he,scale_zeroSpace hr] at hmem
  have hd : (C r * X : Polynomial K).natDegree≤1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have h := hs _ (Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul hP hd).trans (by simp))) hmem
  have h' := congrArg (fun Q : Polynomial K => Q.comp (C r⁻¹ * X)) h
  rw [zero_comp,comp_assoc,C_mul_comp,X_comp,← mul_assoc,← C_mul,mul_inv_cancel₀ hr,C_1,
    one_mul,comp_X] at h'
  exact h'

theorem sum_on_prefix {k : ℕ} (hk : k≤s) (w : Fin s → K)
    (hw : ∀ j, k≤j.val → w j=0) :
    (∑ j : Fin k, w (Fin.castLE hk j)) = ∑ j : Fin s, w j := by
  classical
  have he : Finset.map (Fin.castLEEmb hk) Finset.univ =
      Finset.univ.filter (fun j : Fin s => j.val<k) := by
    ext j
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨l,rfl⟩
      exact l.isLt
    · intro hj
      exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩
  change (∑ j ∈ Finset.univ, w ((Fin.castLEEmb hk) j)) = _
  rw [← Finset.sum_map,he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val<k
  · simp [hj]
  · simp [hj,hw j (by omega)]

def prefixTableau (A : Fin s → Fin s → K) {k : ℕ} (hk : k≤s)
    (i j : Fin k) : K := A (Fin.castLE hk i) (Fin.castLE hk j)

theorem prefix_strict {A : Fin s → Fin s → K} (ha : StrictLower A) {k : ℕ} (hk : k≤s) :
    StrictLower (prefixTableau A hk) :=
  fun i j hij => ha (Fin.castLE hk i) (Fin.castLE hk j) hij

theorem prefix_mat_comm {A : Fin s → Fin s → K} (ha : StrictLower A) {k : ℕ} (hk : k≤s)
    (v : Vec K s) : mat (prefixTableau A hk) (restrictCol (Fin.castLE hk) v) =
      restrictCol (Fin.castLE hk) (mat A v) := by
  ext i
  exact sum_on_prefix hk (fun j => A (Fin.castLE hk i) j * v j)
    (fun j hj => by rw [ha _ _ (by have := i.isLt; exact le_trans i.isLt.le hj),zero_mul])

theorem prefix_tree {A : Fin s → Fin s → K} (ha : StrictLower A)
    {k : ℕ} (hk : k≤s) (t : Tree) :
    restrictCol (Fin.castLE hk) (stageWeight A t) = stageWeight (prefixTableau A hk) t :=
  restrict_stageWeight A _ _ t.order (fun v _ => prefix_mat_comm ha hk v) t (by omega)

theorem normTree_at_clean {A : Fin s → Fin s → K} (q : ℕ) (i : Fin s)
    (hi : ∀ v ∈ zeroSpace A q, v i=0) (t : Tree) (ht : t.order≤q+1) :
    normTree A t i=nodes A i^(t.order-1) := by
  have he : (Tree.bush (t.order-1)).order=t.order := by
    rw [Tree.order_bush]; have := t.order_pos; omega
  have h := hi _ (normDiff_mem A t _ he.symm ht)
  change normTree A t i - normTree A (Tree.bush (t.order-1)) i = 0 at h
  simpa [normTree_bush] using sub_eq_zero.mp h

/-- Exact primitive evaluation at a nonzero stage is a genuine smaller
tableau with the claimed order, not merely a quadrature rule. -/
theorem exact_receiver_prefix_order {A : Fin s → Fin s → K} (ha : StrictLower A) (q : ℕ)
    (i : Fin s) (hu : nodes A i≠0) (hi : ∀ v ∈ zeroSpace A q, v i=0) :
    HasTreeOrderAtLeast (scaleTableau (nodes A i)⁻¹ (prefixTableau A i.isLt.le))
      (fun j => (nodes A i)⁻¹ * A i (Fin.castLE i.isLt.le j)) q := by
  intro t ht
  let r := (nodes A i)⁻¹
  have hclean := normTree_at_clean q i hi (t.attach .leaf) (by
    change t.order+1≤q+1; omega)
  rw [normTree_unary] at hclean
  have horder : (t.attach Tree.leaf).order - 1 = t.order := by simp [Tree.order]
  rw [horder] at hclean
  simp only [Pi.smul_apply, smul_eq_mul,mat_apply,normTree,Finset.mul_sum] at hclean
  have hc : (t.density:K) * (∑ j, A i j * stageWeight A t j) = nodes A i^t.order := by
    rw [← hclean,Tree.density,Nat.cast_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : weight (scaleTableau r (prefixTableau A i.isLt.le))
      (fun j => r * A i (Fin.castLE i.isLt.le j)) t =
      r^t.order * (∑ j, A i j * stageWeight A t j) := by
    rw [weight,stageWeight_scale,← prefix_tree ha]
    simp only [Pi.smul_apply,smul_eq_mul,restrictCol_apply]
    have hterm (j : Fin i.val) :
        r * A i (Fin.castLE i.isLt.le j) * (r^(t.order-1) * stageWeight A t (Fin.castLE i.isLt.le j)) =
        r^t.order * (A i (Fin.castLE i.isLt.le j) * stageWeight A t (Fin.castLE i.isLt.le j)) := by
      have ht := t.order_pos
      have he : r * r^(t.order-1) = r^t.order := by
        rw [← pow_succ']; congr 1; omega
      rw [← he]; ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j),← Finset.mul_sum]
    rw [sum_on_prefix i.isLt.le (fun j => A i j * stageWeight A t j)
      (fun j hj => by rw [ha _ _ hj,zero_mul])]
  change (t.density:K) * weight (scaleTableau r (prefixTableau A i.isLt.le))
    (fun j => r * A i (Fin.castLE i.isLt.le j)) t = 1
  rw [hs,mul_left_comm,hc,← mul_pow]
  simp [r,hu]

theorem clean_five_receiver_has_six_predecessors {A : Fin s → Fin s → K}
    (ha : StrictLower A) (i : Fin s) (hu : nodes A i≠0)
    (hi : ∀ v ∈ zeroSpace A 5, v i=0) : 6 ≤ i.val := by
  have ht := exact_receiver_prefix_order ha 5 i hu hi
  have hs := uniform_erk_field (scale_strict (prefix_strict ha i.isLt.le) _) ht
  omega

end RKCert.Paired
