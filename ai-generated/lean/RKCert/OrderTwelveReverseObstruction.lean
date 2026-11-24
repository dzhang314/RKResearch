module
public import RKCert.ReverseTwoNodeCausality
public import RKCert.OrderTwelveReversePhysical

@[expose] public section
/-! # The actual order-twelve backward quadratic line is not clock invariant
The change of feature h=Yv+(2/a)d absorbs the local defect even if a is
one of the first two h sites. It avoids root-order, positivity, and
nonzero individual-weight assumptions.
-/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.ReverseTwoNode Module
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- Homogeneous change of feature for the one-node-supported quadratic jet. -/
theorem reduce_reverse_rows {N : Vec K s →ₗ[K] Vec K s} {y v d g : Vec K s} {a : K}
    (ha : a≠0) (r : ReverseRows N y v d g a) :
    TwoNodeRows N y (powerWeight y v 1+(2/a) • d) (a⁻¹ • g) := by
  let h := powerWeight y v 1+(2/a) • d
  let G := a⁻¹ • g
  have hval (i) : h i=y i*v i+(2/a)*d i := by simp [h,powerWeight]
  have scaled (k:ℕ) : powerWeight y h k=powerWeight y v (k+1)+((2/a)*a^k) • d := by
    ext i
    simp only [powerWeight,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [hval]
    by_cases he : y i=a
    · rw [he]; ring
    · rw [r.support i he]; ring
  have dG : diag y G=a⁻¹ • diag y g := by ext i; simp [G]; ring
  obtain ⟨b,eb⟩:=r.cubic
  obtain ⟨q,l,eq⟩:=r.quartic
  obtain ⟨k,e,ek⟩:=r.advance
  obtain ⟨m,f,z,em⟩:=r.shifted
  change TwoNodeRows N y h G
  refine ⟨?_,⟨a*(b+2),?_⟩,⟨a*(q+2*a),a*l,?_⟩,⟨k,e,?_⟩,⟨m,f,z,?_⟩⟩
  · intro i; change N (powerWeight y v 1+(2/a) • d) i=_
    rw [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r.next,r.quadratic,hval]
    change _= _+2*(a⁻¹*g i)
    by_cases he : y i=a
    · rw [he]; field_simp
    · rw [r.support i he]; field_simp; ring
  · intro i
    rw [scaled 1,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r.next,eb,hval]
    change _= _+_*(a⁻¹*g i)
    by_cases he : y i=a
    · rw [he]; field_simp; ring
    · rw [r.support i he]; field_simp; ring
  · intro i
    rw [scaled 2,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r.next,eq,hval]
    change _= _+_*(a⁻¹*g i)
    by_cases he : y i=a
    · rw [he]; field_simp; ring
    · rw [r.support i he]; field_simp; ring
  · intro i; simp only [G,map_smul,Pi.smul_apply,smul_eq_mul,ek]; ring
  · intro i; rw [dG,map_smul,Pi.smul_apply,smul_eq_mul,em]
    change _= _*(a⁻¹*g i); ring

/-- Appendix A with no assumptions beyond actual saturation and tree order. -/
theorem back_one_noninvariant {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b) :
    ¬ (back A b 1).map (diag (mirror A))≤back A b 1 := by
  classical
  intro hC
  obtain ⟨a,ha0,r⟩ := localized_reverse_rows ha ho hs hC
  let y := mirror A
  let d := reverseResidual A b 1
  let g := transMat A d
  let h := powerWeight y b 1+(2/a) • d
  have val (i) : h i=y i*b i+(2/a)*d i := by simp [h,powerWeight]
  have loc (i) (hi : y i≠a) : d i=0 := r.support i hi
  have rz : ∀i,y i=0→h i=0 := by
    intro i hi
    rw [val,loc i (by rw [hi]; exact ha0.symm),hi]; ring
  apply two_node_confinement Fin.revPerm (transMat A) (causal_transpose ha) y h
    (a⁻¹ • g) (reduce_reverse_rows ha0 r) rz
  intro t u
  let T : Finset K := {0,a,t,u}
  have card : T.card≤4 := calc
    T.card ≤ ({a,t,u}:Finset K).card+1 := Finset.card_insert_le ..
    _ ≤ (({t,u}:Finset K).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) _
    _ ≤ ((({u}:Finset K).card+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le ..) _) _
    _ = 4 := by simp
  obtain ⟨i,bi,hi⟩ := reflected_active_avoid ho T (by omega)
  have hh : y i≠0 ∧ y i≠a ∧ y i≠t ∧ y i≠u := by
    change y i∉({0,a,t,u}:Finset K) at hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
  exact ⟨i,by rw [val,loc i hh.2.1,mul_zero,add_zero]; exact mul_ne_zero hh.1 bi,hh.2.2⟩

/-- The last remaining chronological escape fills the entire physical stage space. -/
theorem saturated_e9_escape {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b) :
    ¬(treeSpace A 9).map (diag (nodes A))≤treeSpace A 9 := by
  intro hC
  apply back_one_noninvariant ha ho hs
  have h := (reverse_seven_nine ha ho hs).back1
  rw [h]
  rintro _ ⟨v,hv,rfl⟩
  apply mem_annih.mpr
  intro w hw
  rw [row_flip_diag]
  apply mem_annih.mp hv
  have e : diag (mirror A) w=w-diag (nodes A) w := by ext i; simp [mirror,sub_mul]
  rw [e]; exact (treeSpace A 9).sub_mem hw (hC (Submodule.mem_map_of_mem hw))

theorem saturated_e10_top {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b) :
    treeSpace A 10=⊤ := by
  have r9 := (reverse_seven_nine ha ho hs).rank9
  have he := tree_rank_lt_of_clock_escape A 9 (saturated_e9_escape ha ho hs)
  change finrank K (treeSpace A 9)<finrank K (treeSpace A 10) at he
  have size := hs.size
  apply Submodule.eq_of_le_of_finrank_le le_top
  simpa only [finrank_top,Vec,Module.finrank_fin_fun] using
    (show s+1≤finrank K (treeSpace A 10) by omega)

/-- The full chart holds for an actual candidate of at most seventeen stages. -/
theorem actual_e10_top {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hsize : s+1≤17) :
    treeSpace A 10=⊤ :=
  saturated_e10_top ha ho (saturation ha ho
    (grade_five_surplus ha (explicit_separated ha ho (q:=5) (by decide) (by omega))) hsize)

end RKCert.Paired.OrderTwelve
