module
public import RKCert.ReverseHermiteMass

@[expose] public section

/-! # A two-dimensional reverse gain rules out invariant E7 and E8
The tests use the actual transposed tableau, the reflected physical nodes and
the original weight vector. All chronological and grading hypotheses are stated.
-/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint Polynomial
open scoped Classical
variable {K : Type*} [Field K] {s p : ℕ}

/-- Reverse the physical order so the transpose is strictly causal in Fin's usual order. -/
def revVec : Vec K s ≃ₗ[K] Vec K s := LinearEquiv.funCongrLeft K K Fin.revPerm

@[simp] theorem revVec_apply (v : Vec K s) (i : Fin s) : revVec v i=v i.rev := rfl
@[simp] theorem revVec_symm_apply (v : Vec K s) (i : Fin s) :
    (revVec (K:=K) (s:=s)).symm v i=v i.rev := rfl

def reverseOp (A : Fin s → Fin s → K) : Vec K s →ₗ[K] Vec K s :=
  revVec.toLinearMap.comp ((transMat A).comp revVec.symm.toLinearMap)

theorem reverseOp_rev (A : Fin s → Fin s → K) (w : Vec K s) :
    reverseOp A (revVec w)=revVec (transMat A w) := by
  change revVec (transMat A (revVec.symm (revVec w)))=_
  rw [LinearEquiv.symm_apply_apply]

theorem reverseOp_strict {A : Fin s → Fin s → K} (ha : StrictLower A) :
    StrictlyCausal (reverseOp A) := by
  intro i x y hp
  have he := causal_transpose ha i.rev (revVec.symm x-revVec.symm y) (fun j hj => by
    change x j.rev-y j.rev=0
    apply sub_eq_zero.mpr
    exact hp j.rev (by change j.rev.val < i.val; simpa using hj))
  change transMat A (revVec.symm x) i.rev=transMat A (revVec.symm y) i.rev
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using he

theorem reflected_mask_annih {A : Fin s → Fin s → K} {E : Submodule K (Vec K s)}
    (hm : MaskInvariant (nodes A) E) : MaskInvariant (mirror A) (annih E) := by
  classical
  intro a w hw
  apply mem_annih.mpr
  intro x hx
  have hi := mem_annih.mp hw _ (hm (1-a) x hx)
  convert hi using 1
  simp only [row_apply]
  apply Finset.sum_congr rfl
  intro i _
  have e : mirror A i=a ↔ nodes A i=1-a := by
    change 1-nodes A i=a ↔ nodes A i=1-a
    constructor <;> intro h <;> linear_combination -h
  change (if mirror A i=a then w i else 0)*x i=w i*(if nodes A i=1-a then x i else 0)
  rw [e]
  split <;> simp

variable [CharZero K]

/-- Actual-weight reverse Hermite gain for any block-invariant backward space.
Only the two indicated inclusions are required. -/
theorem back_mask_rank_jump {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hp : j+5≤p)
    (hu : back A b n≤annih (treeSpace A (j+1)))
    (hz : annih (treeSpace A j)≤back A b (n+1))
    (hmask : MaskInvariant (mirror A) (back A b n)) :
    Module.finrank K (back A b n)+2 ≤ Module.finrank K (back A b (n+1)) := by
  classical
  let U := back A b n
  let Z := back A b (n+1)
  let T := revVec (K:=K) (s:=s)
  let Ur := U.map T.toLinearMap
  let Zr := Z.map T.toLinearMap
  let y := mirror A
  have hUZ : U≤Z := back_le_succ A b n
  have hNZ (w) (hw : w∈U) : transMat A w∈Z :=
    (le_sup_right.trans (le_sup_left.trans le_sup_left) : U.map (transMat A)≤Z)
      (Submodule.mem_map_of_mem hw)
  have hm : MaskInvariant y U := hmask
  have hrm : MaskInvariant (T y) Ur := by
    intro a w hw
    obtain ⟨x,hx,rfl⟩ := hw
    exact Submodule.mem_map_of_mem (hm a x hx)
  have hmass (w) (hw : w∈Ur) : (∑i,w i)=0 := by
    obtain ⟨x,hx,rfl⟩ := hw
    change x∈back A b n at hx
    have h := mem_annih.mp (hu hx) (1:Vec K s) (stageWeight_mem_space A .leaf (by simp [Tree.order]))
    change (∑i : Fin s, x i.rev)=0
    rw [show (∑i : Fin s, x i.rev)=∑i,x i from Equiv.sum_comp Fin.revPerm x]
    simpa [row_apply] using h
  have rsum (k : ℕ) : (∑i,(T y i)^k*(T b i))=∑i,(y i)^k*b i :=
    Equiv.sum_comp Fin.revPerm (fun i => y i^k*b i)
  obtain ⟨m1,m2,m3⟩ := mirror_moments ho (by omega)
  have nod := two_failed_of_three_moments (T y) (T b) Ur hrm hmass ((rsum 1).trans m1)
    ((rsum 2).trans m2) ((rsum 3).trans m3)
  have wc (P : K[X]) : weightedEval (T y) (T b) P = T (weightedEval y b P) := by
    ext i
    simp only [T,revVec_apply,weightedEval_apply]
  have rank := outgoing_nodal_gain (T y) (T b) Ur Zr (reverseOp A) (reverseOp_strict ha) hrm
    (Submodule.map_mono hUZ) (by
      rintro _ ⟨x,hx,rfl⟩
      rw [show T.toLinearMap x=revVec x from rfl,reverseOp_rev]
      exact Submodule.mem_map_of_mem (hNZ x hx)) 2 nod (by
        intro P hP
        rw [wc,wc,show T=revVec from rfl,reverseOp_rev,←map_sub]
        apply Submodule.mem_map_of_mem
        change _∈back A b (n+1)
        exact hz (reverse_primitive_annih ho j hp P (by omega)))
  rw [←(T.submoduleMap U).finrank_eq,←(T.submoduleMap Z).finrank_eq] at rank
  exact rank

/-- Adjacent exact annihilators and forward clock invariance force reverse rank growth by two.
For p=12, predecessor levels j=6,7 correspond to the two desired forward spaces E7,E8. -/
theorem invariant_reverse_rank_jump {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hp : j+5≤p)
    (hu : back A b n=annih (treeSpace A (j+1)))
    (hz : back A b (n+1)=annih (treeSpace A j))
    (hC : (treeSpace A (j+1)).map (diag (nodes A))≤treeSpace A (j+1)) :
    Module.finrank K (back A b n)+2 ≤ Module.finrank K (back A b (n+1)) := by
  apply back_mask_rank_jump ha ho j n hp hu.le hz.ge
  rw [hu]
  exact reflected_mask_annih (maskInvariant_of_diag (fun _ hx => hC (Submodule.mem_map_of_mem hx)))

/-- Invariance of the backward reflected-clock space itself also forces the two gains. -/
theorem backward_invariant_rank_jump {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hp : j+5≤p)
    (hu : back A b n≤annih (treeSpace A (j+1))) (hz : annih (treeSpace A j)≤back A b (n+1))
    (hC : (back A b n).map (diag (mirror A))≤back A b n) :
    Module.finrank K (back A b n)+2 ≤ Module.finrank K (back A b (n+1)) := by
  classical
  let U := back A b n
  have hcl (v : Vec K s) (hv : v∈U) : diag (nodes A) v∈U := by
    have he : diag (nodes A) v=v-diag (mirror A) v := by ext i; simp [mirror,sub_mul]
    rw [he]; exact U.sub_mem hv (hC (Submodule.mem_map_of_mem hv))
  have hm := maskInvariant_of_diag hcl
  apply back_mask_rank_jump ha ho j n hp hu hz
  intro a w hw
  have eq : blockMask (mirror A) a w=blockMask (nodes A) (1-a) w := by
    ext i
    have he : mirror A i=a ↔ nodes A i=1-a := by
      change 1-nodes A i=a ↔ nodes A i=1-a
      constructor <;> intro h <;> linear_combination -h
    simp only [blockMask,he]
  rw [eq]
  exact hm (1-a) w hw

theorem not_invariant_of_reverse_rank_two {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hp : j+5≤p)
    (hu : back A b n=annih (treeSpace A (j+1))) (hz : back A b (n+1)=annih (treeSpace A j))
    (hr : Module.finrank K (back A b (n+1))≤Module.finrank K (back A b n)+1) :
    ¬(treeSpace A (j+1)).map (diag (nodes A))≤treeSpace A (j+1) := by
  intro h
  have := invariant_reverse_rank_jump ha ho j n hp hu hz h
  omega

end RKCert.Paired.ReverseHull
