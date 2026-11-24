module
public import RKCert.DirkHermite
public import RKCert.DirkPolynomialMarked
public import RKCert.DiagonalHead
@[expose] public section
namespace RKCert.Paired.ReverseHermite
open RKCert.Endpoint Polynomial Module
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- Coordinate order reversal, only on vectors and subspaces: not a
hypothesis of rooted-tree order for a reflected tableau. -/
def rev : Vec K s ≃ₗ[K] Vec K s where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rev_apply (x:Vec K s) (i:Fin s) : rev x i=x i.rev := rfl
@[simp] theorem rev_rev (x:Vec K s) : rev (rev x)=x := by ext i; simp

def revN (A:Fin s→Fin s→K) : Vec K s→ₗ[K]Vec K s :=
  rev.toLinearMap.comp ((transMat A).comp rev.toLinearMap)

@[simp] theorem revN_rev (A:Fin s→Fin s→K) (x:Vec K s) :
    revN A (rev x)=rev (transMat A x) := by simp [revN]

theorem revN_causal (ha :LowerArray A) : InclusiveCausal (revN A) := by
  intro i x y h
  change (∑k:Fin s,A k i.rev*x k.rev)=(∑k:Fin s,A k i.rev*y k.rev)
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : i.rev≤k
  · have hk' : k.rev ≤ i := by simpa using (Fin.rev_le_rev.mpr hk)
    rw [h _ hk']
  · rw [ha k i.rev (lt_of_not_ge hk),zero_mul,zero_mul]

@[simp] theorem rev_weighted (c w:Vec K s) (Q:K[X]) :
    rev (weightedEval c w Q)=weightedEval (rev c) (rev w) Q := rfl

def flipSpace (U:Submodule K (Vec K s)) : Submodule K (Vec K s) := U.map rev.toLinearMap

theorem flip_rank (U:Submodule K (Vec K s)) : finrank K (flipSpace U)=finrank K U :=
  LinearEquiv.finrank_map_eq rev U

theorem flip_mask (c:Vec K s) (U:Submodule K (Vec K s)) (inv:U.map (diag c)≤U) :
    MaskInvariant (rev c) (flipSpace U) := by
  intro z w hw
  obtain ⟨v,hv,rfl⟩:=hw
  exact ⟨Clock.fiber c z v,Clock.fiber_mem inv z hv,rfl⟩

/-- Every net-active forward clock except 1 detects a nonzero reflected
block of the physical scalar weight, even for arbitrarily signed repeated
knots and after restriction to any invariant marked subspace. -/
theorem failures [CharZero K] (ho:HasTreeOrderAtLeast A b p) {j:ℕ}
    {U:Submodule K (Vec K s)} (hU:U≤marked A p j)
    (inv:U.map (diag (mirror A))≤U) :
    p/2≤(failedNodes (rev (mirror A)) (rev b) (flipSpace U) s).card+1 := by
  classical
  let S:=activeNonzero (nodes A) b
  have inc:(S.erase 1).image (fun x:K => 1-x) ⊆
      failedNodes (rev (mirror A)) (rev b) (flipSpace U) s := by
    intro z hz
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hz
    have a1:=Finset.ne_of_mem_erase ha
    have hav:=Finset.mem_of_mem_erase ha
    obtain ⟨_,_,hnet⟩:=Finset.mem_filter.mp hav
    apply mem_failedNodes.mpr
    refine ⟨sub_ne_zero.mpr (Ne.symm a1),?_⟩
    rintro ⟨_,⟨w,hw,rfl⟩,rows⟩
    have eqb (i:Fin s) (hi:nodes A i=a) : w i=b i := by
      have hy : rev (mirror A) i.rev=1-a := by simp [mirror,hi]
      have h:=rows i.rev i.rev.isLt hy
      simpa using h
    have hz := leaf_marked_zero (hU (Clock.fiber_mem inv (1-a) hw))
    have hsum:row (Clock.fiber (mirror A) (1-a) w) 1 = combinedMass (nodes A) b a := by
      rw [row_apply,combinedMass,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : nodes A i=a
      · simp [Clock.fiber,mirror,hi,eqb i hi]
      · simp [Clock.fiber,mirror,hi]
    exact hnet (hsum.symm.trans hz)
  have card:=Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (show Function.Injective (fun x:K=>1-x) from fun x y h => by dsimp at h; linear_combination -h)] at card
  have old:=activeNonzero_card_of_treeOrder ho
  change p/2≤S.card at old
  by_cases h:1∈S
  · rw [Finset.card_erase_of_mem h] at card; omega
  · rw [Finset.erase_eq_of_notMem h] at card; omega

variable [CharZero K]

omit [CharZero K] in
private theorem flip_primitive (P:K[X]) :
    rev (transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)) =
    revN A (weightedEval (rev (mirror A)) (rev b) P) -
      weightedEval (rev (mirror A)) (rev b) (formalPrimitive P) := by
  have h:=revN_rev A (weightedEval (mirror A) b P)
  rw [rev_weighted] at h
  rw [map_sub,rev_weighted,h]

/-- The inclusive weighted Hermite detector theorem in physical reverse
chronology. It can be instantiated with the whole marked flag or any
terminal-zero subflag, with no positive-weights assumption. -/
theorem outgoing (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j r:ℕ} (hp:2*r+2≤p) {U Z:Submodule K (Vec K s)} (hU:U≤marked A p j)
    (inv:U.map (diag (mirror A))≤U) (hUZ:U≤Z) (hNU:∀v∈U,transMat A v∈Z)
    (hP:∀P:K[X], P.natDegree≤2*r →
      transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)∈Z) :
    finrank K U+r≤finrank K Z := by
  rw [←flip_rank U,←flip_rank Z]
  apply outgoing_inclusive_gain (rev (mirror A)) (rev b) (flipSpace U) (flipSpace Z) (revN A)
    (revN_causal ha) (flip_mask _ _ inv) (Submodule.map_mono hUZ) _ r _ _
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨_,hNU v hv,(revN_rev A v).symm⟩
  · have c:=failures ho hU inv
    omega
  · intro P h
    exact ⟨_,hP P (by omega),flip_primitive P⟩

theorem incoming (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j r:ℕ} (hp:2*r+2≤p) {V U:Submodule K (Vec K s)} (hU:U≤marked A p j)
    (inv:U.map (diag (mirror A))≤U) (hVU:V≤U) (hNV:∀v∈V,transMat A v∈U)
    (hP:∀P:K[X], P.natDegree≤2*r →
      transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)∈U) :
    finrank K V+r≤finrank K U := by
  rw [←flip_rank V,←flip_rank U]
  apply incoming_inclusive_gain (rev (mirror A)) (rev b) (flipSpace V) (flipSpace U) (revN A)
    (revN_causal ha) (flip_mask _ _ inv) (Submodule.map_mono hVU) _ r _ _
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨_,hNV v hv,(revN_rev A v).symm⟩
  · have c:=failures ho hU inv
    omega
  · intro P h
    exact ⟨_,hP P (by omega),flip_primitive P⟩

/-- Any clock-invariant part of the full marked flag at grade j pays a
floor(j/2) outgoing gain in the genuine next marked space. -/
theorem full_outgoing (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (hp:j+2≤p) {U:Submodule K (Vec K s)} (hU:U≤marked A p j)
    (inv:U.map (diag (mirror A))≤U) : finrank K U + j/2 ≤ finrank K (marked A p (j+1)) := by
  apply outgoing ha ho (by omega) hU inv (hU.trans (marked_mono A p (by omega)))
    (fun v hv => marked_mat hp (hU hv))
  intro P h
  exact weighted_reverse_primitive ho (by omega) hp

theorem full_incoming (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (hp:j+2≤p)
    (inv:(marked A p (j+1)).map (diag (mirror A))≤marked A p (j+1)) :
    finrank K (marked A p j)+j/2≤finrank K (marked A p (j+1)) := by
  apply incoming ha ho (by omega) le_rfl inv (marked_mono A p (by omega)) (fun v hv=>marked_mat hp hv)
  intro P h
  exact weighted_reverse_primitive ho (by omega) hp

/-- An actual original-coordinate terminal restriction, not a shortened RK
method or an order assumption on an adjoint scheme. -/
def zeroMarked (A : Fin s→Fin s→K) (p:ℕ) (t:Fin s) (j:ℕ) : Submodule K (Vec K s) :=
  marked A p j ⊓ LinearMap.ker (LinearMap.proj t)

omit [CharZero K] in
theorem zeroMarked_mono (A : Fin s→Fin s→K) (p:ℕ) (t:Fin s) : Monotone (zeroMarked A p t) :=
  fun _ _ h => inf_le_inf_right _ (marked_mono A p h)

omit [CharZero K] in
theorem trans_terminal (t:Fin s) (col:∀i,A i t=0) (v:Vec K s) :
    transMat A v t=0 := by
  change (∑i:Fin s,A i t*v i)=0
  simp [col]

theorem terminal_primitive (ho:HasTreeOrderAtLeast A b p) {j:ℕ} (hp:j+2≤p)
    (t:Fin s) (ht:nodes A t=1) (col:∀i,A i t=0) (P:K[X]) (hd:P.natDegree≤j) :
    transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)
      ∈zeroMarked A p t (j+1) := by
  refine ⟨weighted_reverse_primitive ho hd hp,?_⟩
  change transMat A _ t-(weightedEval (mirror A) b (formalPrimitive P)) t=0
  simp [trans_terminal t col,mirror,ht]

theorem terminal_outgoing (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (hp:j+2≤p) (t:Fin s) (ht:nodes A t=1) (col:∀i,A i t=0)
    {U:Submodule K (Vec K s)} (hU:U≤zeroMarked A p t j)
    (inv:U.map (diag (mirror A))≤U) :
    finrank K U+j/2≤finrank K (zeroMarked A p t (j+1)) := by
  apply outgoing ha ho (by omega) (hU.trans inf_le_left) inv (hU.trans (zeroMarked_mono A p t (by omega)))
    (fun v hv => ⟨marked_mat hp (hU hv).1,trans_terminal t col v⟩)
  intro P h
  exact terminal_primitive ho hp t ht col P (by omega)

theorem terminal_incoming (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (hp:j+2≤p) (t:Fin s) (ht:nodes A t=1) (col:∀i,A i t=0)
    (inv:(zeroMarked A p t (j+1)).map (diag (mirror A))≤zeroMarked A p t (j+1)) :
    finrank K (zeroMarked A p t j)+j/2≤finrank K (zeroMarked A p t (j+1)) := by
  apply incoming ha ho (by omega) inf_le_left inv (zeroMarked_mono A p t (by omega))
    (fun v hv => ⟨marked_mat hp hv.1,trans_terminal t col v⟩)
  intro P h
  exact terminal_primitive ho hp t ht col P (by omega)

/-- A genuine rank increment of one cannot leave either marked flag
clock-invariant once the two-detector budget has been paid. -/
theorem terminal_escape_out (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (hp:j+2≤p) (hj:4≤j) (t:Fin s) (ht:nodes A t=1) (col:∀i,A i t=0)
    (one:finrank K (zeroMarked A p t (j+1))≤finrank K (zeroMarked A p t j)+1) :
    ¬(zeroMarked A p t j).map (diag (mirror A))≤zeroMarked A p t j := by
  intro inv
  have h:=terminal_outgoing ha ho hp t ht col (le_refl _) inv
  omega

theorem terminal_escape_in (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (hp:j+2≤p) (hj:4≤j) (t:Fin s) (ht:nodes A t=1) (col:∀i,A i t=0)
    (one:finrank K (zeroMarked A p t (j+1))≤finrank K (zeroMarked A p t j)+1) :
    ¬(zeroMarked A p t (j+1)).map (diag (mirror A))≤zeroMarked A p t (j+1) := by
  intro inv
  have h:=terminal_incoming ha ho hp t ht col inv
  omega

end
end RKCert.Paired.ReverseHermite
