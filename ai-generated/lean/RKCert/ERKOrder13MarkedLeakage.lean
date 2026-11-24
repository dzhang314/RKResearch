module
public import RKCert.ERKOrder13FirstLeak

@[expose] public section
/-! # Three actual paid shifts eliminate marked grade-eight leakage
The alias chart pays one extra defect grade after subtracting its head.
Both marked ghost planes are exhausted by the fixed exact row identities;
no integrality, order topology or numerical root data enter this step.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2800000

omit [CharZero K] in
inductive MarkGhost13 (P:K[X]) : ℕ→Prop
  | unaliased (x y:K) (eq:P=x•dx4+y•dx5) : MarkGhost13 P 6
  | aliased (x y:K) (eq:P=x•dx3+y•dx4) : MarkGhost13 P 5

theorem marked13_decompose (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    {v:Vec K (s+1)} (hv:v∈defectPlus A 1 8) :
    ∃ P:K[X],P.natDegree≤a∧MarkGhost13 P a∧v-evalNodes A P∈Band13 A a r U w 8 := by
  classical
  have width:=C.width
  have he : v∈treePlus A 1 8 := (sup_le_sup (zeroSpace_le_treeSpace A 8) le_rfl) hv
  rw [C.chart 8 (by omega) (by decide)] at he
  obtain ⟨u,⟨c,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp he
  let P:=ofFn (a+1) c
  have pd:P.natDegree≤a := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have ev:evalNodes A P=polyEval A a c:=evalNodes_ofFn A a c
  have zpaid:=band13_paid C (j:=8) (by omega) hz
  have vp : v∈defectPlus A 1 (8+(6-a)) := Fplus_mono A 1 (by omega) hv
  have pp : evalNodes A P∈defectPlus A 1 (8+(6-a)) := by
    rw [ev,show polyEval A a c=v-z by rw [←eq];abel]
    exact Submodule.sub_mem _ vp zpaid
  have o:=marked_eval_origin ha (by have:=S.size;omega) P pp
  refine ⟨P,pd,?_,by rw [ev,←eq];simpa only [add_sub_cancel_left] using hz⟩
  have ar:a=6∨a=5:=by omega
  rcases ar with rfl|rfl
  · obtain ⟨t,u,e⟩:=ghost13Prefix_decode P pd o (fun k=>marked_moment_difference ho P pp
      (by omega) M.atOne (by have:=k.isLt;omega))
    exact .unaliased t u e
  · obtain ⟨t,u,e⟩:=ghost13Alias_decode P pd o (fun k=>marked_moment_difference ho P pp
      (by omega) M.atOne (by have:=k.isLt;omega))
    exact .aliased t u e

theorem marked13_alias_mesh (C:Chart13 A 1 5 r U w G) :
    ∃ t:K,G=t•dx5 := by
  cases C.mesh with
  | marked x y e =>
    have y0:y=0 := by
      by_contra hy
      have qd := natDegree_smul_le x (dx5:K[X])
      have rd := natDegree_smul (dx6:K[X]) hy
      have gd := C.meshDegree
      rw [dx6_degree] at rd
      rw [dx5_degree] at qd
      rw [e,natDegree_add_eq_right_of_natDegree_lt (by omega),rd] at gd
      omega
    refine ⟨x,?_⟩
    simpa only [y0,zero_smul,add_zero] using e

omit [CharZero K] in
private theorem small_shift_ghost_zero {P:K[X]} (gd:G.natDegree=a+1)
    (pd:P.natDegree≤a) {t:K} (h:-P=t•G) : P=0 := by
  by_contra n
  have eq := mesh_line_degree h (neg_ne_zero.mpr n)
  rw [natDegree_neg,gd] at eq
  omega

theorem order13_marked_no_leak (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    {v:Vec K (s+1)} (pv:v∈defectPlus A 1 8)
    (cv:diag (nodes A) v∈defectPlus A 1 8)
    (dv:diag (nodes A) (diag (nodes A) v)∈defectPlus A 1 8) :
    v∈Band13 A a r U w 8 ∧ diag (nodes A) v∈Band13 A a r U w 8 ∧
    diag (nodes A) (diag (nodes A) v)∈Band13 A a r U w 8 := by
  have width:=C.width
  obtain ⟨P,pd,gP,hP⟩:=marked13_decompose ha ho S M C pv
  obtain ⟨Q,qd,gQ,hQ⟩:=marked13_decompose ha ho S M C cv
  obtain ⟨R,rd,gR,hR⟩:=marked13_decompose ha ho S M C dv
  obtain ⟨t,e⟩:=band13_polynomial_shift S M C (by omega) (by decide) pd qd hP hQ
  obtain ⟨u,f⟩:=band13_polynomial_shift S M C (by omega) (by decide) qd rd hQ hR
  have P0:P=0 := by
    rcases (show a=6∨a=5 by omega) with rfl|rfl
    · cases gP with
      | unaliased p0 p1 pfit =>
        cases gQ with
        | unaliased q0 q1 qfit =>
          cases gR with
          | unaliased r0 r1 rfit =>
            cases C.mesh with
            | marked g0 g1 gfit =>
              rw [pfit,qfit,gfit,smul_add,smul_smul,smul_smul] at e
              rw [qfit,rfit,gfit,smul_add,smul_smul,smul_smul] at f
              obtain ⟨z0,z1⟩:=shift13Prefix p0 p1 q0 q1 r0 r1 (t*g0) (t*g1) (u*g0) (u*g1) e f
              rw [pfit,z0,z1,zero_smul,zero_smul,zero_add]
    · obtain ⟨g0,gfit⟩:=marked13_alias_mesh C
      cases gP with
      | aliased p0 p1 pfit =>
        cases gQ with
        | aliased q0 q1 qfit =>
          cases gR with
          | aliased r0 r1 rfit =>
            rw [pfit,qfit,gfit,smul_smul] at e
            rw [qfit,rfit,gfit,smul_smul] at f
            obtain ⟨z0,z1⟩:=shift13Alias p0 p1 q0 q1 r0 r1 (t*g0) (u*g0) e f
            rw [pfit,z0,z1,zero_smul,zero_smul,zero_add]
  have Q0:Q=0 := small_shift_ghost_zero C.meshDegree qd (by rwa [P0,mul_zero,zero_sub] at e)
  have R0:R=0 := small_shift_ghost_zero C.meshDegree rd (by rwa [Q0,mul_zero,zero_sub] at f)
  have zz : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp
  exact ⟨by simpa only [P0,zz,sub_zero] using hP,by simpa only [Q0,zz,sub_zero] using hQ,
    by simpa only [R0,zz,sub_zero] using hR⟩

omit [CharZero K] in
theorem marked13_terminal_in_core (C:Chart13 A 1 a r U w G) :
    tailPlane K s 1≤U := by
  intro x hx
  have xp : x∈defectPlus A 1 5 := (show tailPlane K s 1≤_ from le_sup_right) hx
  rw [C.marked.paid 5 le_rfl (by decide)] at xp
  have rSite:=band13_sites C
  have cnt : r<(headSites (nodes A) w).card := by unfold headLen at rSite;omega
  apply localized_mem (z:=nodes A (Fin.last s)) C.marked.stable C.marked.norm cnt xp
  intro i h
  have il:i≠Fin.last s := fun hh=>h (hh ▸ rfl)
  rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)] at hx
  obtain ⟨m,rfl⟩:=Submodule.mem_span_singleton.mp hx
  rw [Pi.smul_apply,terminal_at_ne il,smul_zero]

end RKCert.Paired.FiniteMidpoint
