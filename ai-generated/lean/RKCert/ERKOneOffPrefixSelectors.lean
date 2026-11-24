module

public import RKCert.ERKOrderNineOneOffCleanClocks
public import RKCert.ERKMergeRows

@[expose] public section

/-! # True raw row comparison in a one-off prefix -/
namespace RKCert.Paired.OneOff
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s→Fin s→K}

def chartNode (a d : K) (i : Fin 4) : K :=
  if i.val=0 then 0 else if i.val=1 then a else if i.val=2 then d else 2*d

def chartDefect (a : K) (i : Fin 4) : K := if i.val=1 then baseAmp a else 0

def chartH (a d : K) (i : Fin 4) : K :=
  if i.val=2 then twoHd a d else if i.val=3 then a*d^2 else 0

/-- Four dual profiles, the three clean-clock quadratics corrected at
the off row, plus the off defect selector. -/
def chartSelectorCoeffs (a d : K) (l : Fin 4) : K × K × K × K :=
  let f0 := 1-3*a/(2*d)+a^2/(2*d^2)
  let f2 := 2*a/d-a^2/d^2
  let f3 := -a/(2*d)+a^2/(2*d^2)
  if l.val=0 then (1,-3/(2*d),1/(2*d^2),-f0/baseAmp a)
  else if l.val=1 then (0,0,0,1/baseAmp a)
  else if l.val=2 then (0,2/d,-1/d^2,-f2/baseAmp a)
  else (0,-1/(2*d),1/(2*d^2),-f3/baseAmp a)

noncomputable def chartSelector (A : Fin s→Fin s→K) (a d : K) (l : Fin 4) : Vec K s :=
  let C := chartSelectorCoeffs a d l
  C.1 • (1:Vec K s)+C.2.1 • nodes A+C.2.2.1 • (nodes A)^2+C.2.2.2 • g A

set_option maxHeartbeats 750000 in
theorem chart_selector_nodes {a d : K} (an : a≠0) (dn : d≠0)
    {r : Fin s} {m : Fin 4} (nc : nodes A r=chartNode a d m)
    (gc : g A r=chartDefect a m) (l : Fin 4) :
    chartSelector A a d l r=if m=l then 1 else 0 := by
  simp only [chartSelector,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply,Pi.one_apply,
    nc,gc]
  fin_cases l <;> fin_cases m <;>
    norm_num [chartSelectorCoeffs,chartNode,chartDefect,baseAmp] <;>
    (try field_simp [an,dn]) <;> (first | exact an | ring)

theorem chart_selector_mem (A : Fin s→Fin s→K) (a d : K) (l : Fin 4) :
    chartSelector A a d l∈treeSpace A 2 := by
  have P1 : (1:Vec K s)∈treeSpace A 2 := stageWeight_mem_space A Tree.leaf (by decide)
  have Pc : nodes A∈treeSpace A 2 := by
    have h := evalNodes_mem_treeSpace A (X:K[X]) (by simp : (X:K[X]).natDegree≤2)
    simpa using h
  have Pc2 : (nodes A)^2∈treeSpace A 2 := by
    have h := evalNodes_mem_treeSpace A ((X:K[X])^2) (by simp : ((X:K[X])^2).natDegree≤2)
    have e : evalNodes A ((X:K[X])^2)=(nodes A)^2 := by ext l; simp
    rwa [e] at h
  have Pg := zeroSpace_le_treeSpace A 2 (qdef_mem A)
  unfold chartSelector
  exact (treeSpace A 2).add_mem
    ((treeSpace A 2).add_mem
      ((treeSpace A 2).add_mem ((treeSpace A 2).smul_mem _ P1) ((treeSpace A 2).smul_mem _ Pc))
      ((treeSpace A 2).smul_mem _ Pc2))
    ((treeSpace A 2).smul_mem _ Pg)

def FirstChartBefore (A : Fin s→Fin s→K) (a d : K) (j : Fin s) : Prop :=
  ∀ r, r < j → ∃ l : Fin 4, l.val=r.val ∧
    nodes A r=chartNode a d l ∧ g A r=chartDefect a l

theorem prefix_row_zero_by_selectors {a d : K} {j : Fin s} {w : Vec K s}
    (an : a≠0) (dn : d≠0) (pre : FirstChartBefore A a d j)
    (sup : ∀ r, j ≤ r → w r=0)
    (ann : ∀ l : Fin 4, row w (chartSelector A a d l)=0) :
    w=0 := by
  ext r
  by_cases old : r < j
  · obtain ⟨l,ll,cn,cg⟩ := pre r old
    have h := ann l
    rw [row_apply,Finset.sum_eq_single r] at h
    · simpa [chart_selector_nodes an dn cn cg l] using h
    · intro u _ ne
      by_cases pu : u < j
      · obtain ⟨m,mm,un,ug⟩ := pre u pu
        have dif : m≠l := by
          intro eq
          apply ne
          exact Fin.ext (mm.symm.trans ((congrArg Fin.val eq).trans ll))
        rw [chart_selector_nodes an dn un ug l,ite_eq_right dif,mul_zero]
      · rw [sup u (le_of_not_gt pu),zero_mul]
    · simp
  · exact sup r (le_of_not_gt old)

/-- Equal current features alone do not imply equal stages. With the
actual independent source rows before the second one, the four
paid actions force equality of every raw matrix coefficient. -/
theorem prefix_equal_physical_rows (ha : StrictLower A) {a d : K} {i j : Fin s}
    (an : a≠0) (dn : d≠0)
    (q2 : mDef A 2=(2*a/3) • g A+twoLam a d • h A)
    (ij : i < j) (pre : FirstChartBefore A a d j)
    (ce : nodes A i=nodes A j) (ge : g A i=g A j) (he : h A i=h A j) :
    ∀ r, A i r=A j r := by
  let w : Vec K s := A i-A j
  have supp (r : Fin s) (jr : j ≤ r) : w r=0 := by
    simp [w,ha _ _ (ij.le.trans jr),ha _ _ jr]
  have row_eq (v : Vec K s) : row w v=mat A v i-mat A v j := by
    simp only [row_apply,w,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib,mat_apply]
  have e1 : row w (1:Vec K s)=0 := by
    rw [row_eq]
    have unit_action (u : Fin s) : mat A (1:Vec K s) u=nodes A u := by simp [nodes,mat_apply]
    rw [unit_action,unit_action,ce,sub_self]
  have em1 : row w (nodes A)=0 := by
    rw [row_eq]
    change M1 A i-M1 A j=0
    rw [m1_relation,m1_relation,ce,ge,sub_self]
  have em2 : row w ((nodes A)^2)=0 := by
    rw [row_eq]
    change M2 A i-M2 A j=0
    rw [m2_relation q2,m2_relation q2,ce,ge,he,sub_self]
  have eg : row w (g A)=0 := by
    rw [row_eq]
    change h A i-h A j=0
    rw [he,sub_self]
  have ann (l : Fin 4) : row w (chartSelector A a d l)=0 := by
    simp only [chartSelector,map_add,map_smul,e1,em1,em2,eg,smul_zero,add_zero]
  have z := prefix_row_zero_by_selectors an dn pre supp ann
  intro r
  exact sub_eq_zero.mp (congrFun z r)

theorem no_repeat_in_first_chart_at_floor {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (floor : max p ((3*p+1)/2-2)=s+1)
    {a d : K} {i j : Fin (s+1)} (an : a≠0) (dn : d≠0)
    (q2 : mDef A 2=(2*a/3) • g A+twoLam a d • h A)
    (ij : i < j) (pre : FirstChartBefore A a d j)
    (ce : nodes A i=nodes A j) (ge : g A i=g A j) (he : h A i=h A j) : False :=
  no_identical_rows_at_uniform_floor ha ho floor ij
    (prefix_equal_physical_rows ha an dn q2 ij pre ce ge he)

end RKCert.Paired.OneOff
