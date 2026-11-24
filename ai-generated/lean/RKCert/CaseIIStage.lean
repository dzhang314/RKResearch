module

public import RKCert.CaseIIFiveRows
public import RKCert.GradeFiveSpace

@[expose] public section

/-! # Actual graded RK stage spaces rule out the single-node quadratic defect branch -/
namespace RKCert.Paired.CaseII
open RKCert.Paired
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
/-- Coefficient form of a single defect adjoined to a clock chain. -/
theorem curve_expansion {A : Fin n → Fin n → K} {v d w : Vec K n} {q : ℕ}
    (h : v∈Submodule.span K {d} ⊔ chainSpan A w q) :
    ∃ a : K, ∃ f : Fin (q+1) → K, ∀i,
      v i=a*d i+(∑ j, f j*nodes A i^j.val)*w i := by
  obtain ⟨v,hv,z,hz,rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hz
  refine ⟨a,f,?_⟩
  intro i
  rw [←hf]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,signal,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _; ring

omit [CharZero K] in
/-- The particular quartic cost is four, not five: all four order-graded tests
that will be applied are taken from the original rooted tree span. -/
theorem quartic_mem (A : Fin n → Fin n → K) (t y : K) :
    mat A (fun j => DQ t y (nodes A j)) - (fun i => Q t y (nodes A i)) ∈ zeroSpace A 4 := by
  let c := nodes A
  have h3 := primitive_mem_zeroSpace A 3
  have h2 := zeroSpace_mono A (by decide : 3≤4) (primitive_mem_zeroSpace A 2)
  have h1 := zeroSpace_mono A (by decide : 2≤4) (primitive_mem_zeroSpace A 1)
  have hv := (zeroSpace A 4).add_mem ((zeroSpace A 4).sub_mem
    ((zeroSpace A 4).smul_mem (2:K) h3) ((zeroSpace A 4).smul_mem (3*t+2*y) h2))
    ((zeroSpace A 4).smul_mem (3*t*y) h1)
  have he : (fun j => DQ t y (c j)) = (8:K) • c^3 - (9*t+6*y) • c^2 + (6*t*y) • c := by
    ext i; simp [DQ,Pi.pow_apply]
  change mat A (fun j => DQ t y (c j)) - (fun i => Q t y (c i)) ∈ _
  rw [he,map_add,map_sub,map_smul,map_smul,map_smul]
  convert hv using 1
  ext i
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  simp only [c,Q,pow_one]
  have ep (k : ℕ) : (fun j => nodes A j ^ k) = (nodes A)^k := rfl
  rw [ep 2,ep 3]
  ring

/-- The single-node case of the degree-five strict stage barrier, with a
normalized second node and no duplicate genuine stage rows through grade five.
Only the first five physical rows need be distinct, but the stronger and
more convenient global row assumption is accepted by this wrapper. -/
theorem compressed_caseII_impossible {A : Fin n → Fin n → K}
    (ha : StrictLower A) (hn : 5≤n) (h1 : nodes A (Fin.castLE hn (1:Fin 5))=1)
    (hs : ∀i, qdef A i=0 ∨ nodes A i=1 ∧ qdef A i= -(1/2:K))
    (h3 : zeroSpace A 3 = Submodule.span K {qdef A} ⊔ chainSpan A (mat A (qdef A)) 0)
    (h4 : zeroSpace A 4 = Submodule.span K {qdef A} ⊔ chainSpan A (mat A (qdef A)) 1)
    (h5 : zeroSpace A 5 = Submodule.span K {qdef A} ⊔ chainSpan A (mat A (qdef A)) 2)
    (hrows : ∀ i j : Fin n, i<j → ∃t : Tree, t.order≤6 ∧ stageWeight A t i≠stageWeight A t j) :
    False := by
  let e := Fin.castLE hn
  let c := nodes A
  let d := qdef A
  let w := mat A d
  let B := prefixTableau A hn
  have hmat (v : Vec K n) (i : Fin 5) : mat B (fun j => v (e j)) i=mat A v (e i) :=
    congrFun (prefix_mat_comm ha hn v) i
  have hcB : (fun i => c (e i))=nodes B := by
    ext i
    simpa [c,nodes,mat_apply] using (hmat (1:Vec K n) i).symm
  have sep (i j : Fin 5) (hij : i<j) (hc : c (e j)=c (e i)) (hd : d (e j)=d (e i))
      (hw : w (e j)=w (e i)) : False := by
    obtain ⟨t,ht,htn⟩ := hrows (e i) (e j) hij
    have hv : stageWeight A t∈treeSpace A 5 := stageWeight_mem_space A t ht
    obtain ⟨P,hP,hpure⟩ := exists_poly_zeroSpace_charZero A hv
    obtain ⟨a,f,h⟩ := curve_expansion (h5 ▸ hpure)
    have hi := h (e i); have hj := h (e j)
    change stageWeight A t (e i)-P.eval (c (e i))=a*d (e i)+(∑j,f j*c (e i)^j.val)*w (e i) at hi
    change stageWeight A t (e j)-P.eval (c (e j))=a*d (e j)+(∑k,f k*c (e j)^k.val)*w (e j) at hj
    rw [hc,hd,hw] at hj
    exact htn (by linear_combination hi-hj)
  have lin3 (x : Vec K n) (h : x∈zeroSpace A 3) :
      ∃a b : K, ∀i,x i=a*d i+b*w i := by
    obtain ⟨a,f,hv⟩ := curve_expansion (h3 ▸ h)
    exact ⟨a,f 0,fun i => by simpa only [Fin.sum_univ_succ,Fin.val_zero,pow_zero,
      mul_one,Finset.univ_eq_empty,Finset.sum_empty,add_zero] using hv i⟩
  have lin4 (x : Vec K n) (h : x∈zeroSpace A 4) :
      ∃a b k : K, ∀i,x i=a*d i+(b+k*c i)*w i := by
    obtain ⟨a,f,hv⟩ := curve_expansion (h4 ▸ h)
    exact ⟨a,f 0,f 1,fun i => by simpa [Fin.sum_univ_succ,c,d,w] using hv i⟩
  have hW : w∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 (qdef_mem A)
  refine five_rows_impossible (A:=B) (prefix_strict ha hn) (fun i=>c (e i)) (fun i=>d (e i))
    (fun i=>w (e i)) hcB h1 ?_ ?_ (fun i => hs (e i)) sep ?_ ?_ ?_ ?_
  · intro i
    rw [hmat]
    change mat A c (e i) - (2:K)⁻¹*c (e i)^2=_
    ring
  · ext i
    exact (hmat d i).symm
  · obtain ⟨a,b,h⟩ := lin3 _ (primitive_mem_zeroSpace A 2)
    refine ⟨a,b,fun i => ?_⟩
    change 3*mat B (fun j => c (e j)^2) i-c (e i)^3=_
    rw [hmat (fun j=>c j^2)]
    exact h (e i)
  · obtain ⟨a,b,k,h⟩ := lin4 _ (mat_zeroSpace_charZero A 3 hW)
    exact ⟨a,b,k,fun i => (hmat w i).trans (h (e i))⟩
  · intro t y
    obtain ⟨a,b,k,h⟩ := lin4 _ (quartic_mem A t y)
    refine ⟨a,b,k,fun i => ?_⟩
    rw [hmat (fun j => DQ t y (c j))]
    exact h (e i)
  · have hC : (fun j => c j*w j)∈zeroSpace A 4 := diag_zeroSpace A 3 hW
    have hR := mat_zeroSpace_charZero A 4 hC
    obtain ⟨a,f,h⟩ := curve_expansion (h5 ▸ hR)
    exact ⟨a,fun x => ∑j, f j*x^j.val,fun i => (hmat (fun j=>c j*w j) i).trans (h (e i))⟩

end RKCert.Paired.CaseII
