module
public import RKCert.ERKOrder13Shifts
public import RKCert.ERKOrder13TerminalDichotomy
public import RKCert.ERKFiniteChart

@[expose] public section

/-! # Actual full and marked order-thirteen bands through grade ten
This secures the ordinary/alias split without asserting the last feature
or backward chronology exclusions. The stage count 19 is still provisional.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 1300000

omit [CharZero K] in
inductive Mesh13 (P:K[X]) : ℕ→Prop
  | full (x:K) (eq:P=x•odd6) : Mesh13 P 0
  | marked (x y:K) (eq:P=x•dx5+y•dx6) : Mesh13 P 1

theorem actual_mesh13 (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 d) (P:K[X]) (pd:P.natDegree≤7)
    (hp:evalNodes A P∈firstEscape A d 6) : Mesh13 P d := by
  have h0:=marked_eval_origin ha (by have := S.size;omega) P (firstEscape_defect hp)
  have k : d≤1 := by have :=M.budget;omega
  interval_cases d
  · obtain ⟨x,hx⟩:=mesh13Full_decode P pd h0
      (fun j => marked_moment_zero ho P (firstEscape_defect hp) pd (by have:=j.isLt;omega))
    exact .full x hx
  · obtain ⟨x,y,hxy⟩:=mesh13Prefix_decode P pd h0
      (fun j => marked_moment_difference ho P (firstEscape_defect hp) pd M.atOne (by have:=j.isLt;omega))
    exact .marked x y hxy

theorem mesh13_alias {P:K[X]} (h:Mesh13 P d) (hd:P.natDegree≤6) (hn:P≠0) :
    d=1 ∧ P.natDegree=6 := by
  cases h with
  | full x e =>
    have eq := (mesh_line_degree e hn).trans odd6_degree
    omega
  | marked x y e =>
    exact ⟨rfl,(mesh_span_degree e (by rw [dx5_degree,dx6_degree];decide)
      (by rwa [dx5_degree]) hn).trans dx5_degree⟩

noncomputable abbrev Band13 (A:Fin (s+1)→Fin (s+1)→K) (a r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (j:ℕ) :=
  forwardBand A 6 a r U w j

structure Chart13 (A:Fin (s+1)→Fin (s+1)→K) (d a r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (G:K[X]) : Prop where
  marked : MarkedHead A 6 d r U w
  shape : a=6 ∨ a=5∧d=1
  mesh : Mesh13 G d
  meshDegree : G.natDegree=a+1
  meshPaid : evalNodes A G∈firstEscape A d 6
  chart : ∀j,a+1≤j→j≤10→treePlus A d j=polyBand A a⊔Band13 A a r U w j
  rich : ∀j,a+1≤j→j≤10→finrank K (treePlus A d j)=j+7+d

omit [CharZero K] in
theorem Chart13.width (C:Chart13 A d a r U w G) : 5≤a∧a≤6 := by
  rcases C.shape with h|h <;> omega

theorem actual_chart13 (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 d) :
    ∃ a r U w G,Chart13 A d a r U w G := by
  classical
  have ho':HasTreeOrderAtLeast A b (2*6+1) := ho
  obtain ⟨r,U,w,H⟩:=marked_head_short ha ho' (by decide) (by decide) S M
  have finalize (a:ℕ) (ht:a=6∨a=5∧d=1) (G:K[X]) (gd:G.natDegree=a+1)
      (gp:evalNodes A G∈firstEscape A d 6)
      (eq:treePlus A d (a+1)=polyBand A a⊔firstEscape A d 6)
      (rr:finrank K (treePlus A d (a+1))=a+1+7+d)
      (rp:finrank K (treePlus A d ((a+1)-1))=(if a+1=6 then 11+d else 6+(a+1)+d)) :
      Chart13 A d a r U w G := by
    have aLe : a≤6 := by rcases ht with h|h <;> omega
    have aLo : 6≤a+1 := by rcases ht with h|h <;> omega
    have stairs := band_staircase_short (q:=6) (ε:=1) (d:=d) (l:=r+2)
      ha ho' (by decide) M aLo (by omega) H.stable
      (by rwa [←H.edge]) (by omega) rp
    have all (j:ℕ) (hj:a+1≤j) (hmax:j≤10) :
        treePlus A d j=polyBand A a⊔Band13 A a r U w j ∧
        finrank K (treePlus A d j)=j+7+d := by
      have e:=stairs (j-(a+1)) (by omega)
      rw [show a+1+(j-(a+1))=j by omega] at e
      exact ⟨e.1,by omega⟩
    exact ⟨H,ht,actual_mesh13 ha ho S M G (by omega) gp,gd,gp,
      fun j hj hm=>(all j hj hm).1,fun j hj hm=>(all j hj hm).2⟩
  by_cases h : ∀ P:K[X],P.natDegree≤6→evalNodes A P∈firstEscape A d 6→P=0
  · obtain ⟨eq,rr,G,gd,gp⟩:=band_start_noalias_short ho' (by decide) M H h
    exact ⟨6,r,U,w,G,finalize 6 (.inl rfl) G gd gp eq (by omega) (by simpa using M.eMid)⟩
  · push Not at h
    obtain ⟨G,gd,gp,gn⟩:=h
    obtain ⟨d1,gdeg⟩:=mesh13_alias (actual_mesh13 ha ho S M G (by omega) gp) gd gn
    have low (P:K[X]) (hd:P.natDegree≤5) (hp:evalNodes A P∈firstEscape A d 6) : P=0 := by
      by_contra hn
      have eq := (mesh13_alias (actual_mesh13 ha ho S M P (by omega) hp) (by omega) hn).2
      omega
    have eq := band_start_alias_short ho' (by decide) M (by decide) S H low G gdeg gp
    exact ⟨5,r,U,w,G,finalize 5 (.inr ⟨rfl,d1⟩) G gdeg gp eq (by simpa using M.eMid) (by simpa using M.ePrev)⟩

omit [CharZero K] in
theorem band13_paid (C:Chart13 A d a r U w G) {j:ℕ} (hj:a+1≤j) :
    Band13 A a r U w j≤defectPlus A d (j+(6-a)) := by
  have base : ∀k,chain (diag (nodes A)) U w (r+2+k)≤defectPlus A d (7+k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero,←C.marked.edge]
      exact firstEscape_defect
    | succ k ih =>
      rw [show r+2+(k+1)=r+2+k+1 by omega,←chain_sup_map (w:=w) C.marked.stable (by omega)]
      exact sup_le (ih.trans (Fplus_mono A d (by omega)))
        (((Submodule.map_mono ih).trans (Fplus_clock A d (7+k))).trans (Fplus_mono A d (by omega)))
  unfold Band13 forwardBand headLen
  exact (base (j-(a+1))).trans (Fplus_mono A d (by have := C.width.2;omega))

omit [CharZero K] in
theorem band13_sites (C:Chart13 A d a r U w G) :
    headLen 6 a r 10≤(headSites (nodes A) w).card := by
  let n:=headLen 6 a r 9
  let D:=diag (nodes A)
  have width:=C.width
  have e9:=C.chart 9 (by omega) (by decide)
  have e10:=C.chart 10 (by omega) (by decide)
  have r9:=C.rich 9 (by omega) (by decide)
  have r10:=C.rich 10 (by omega) (by decide)
  have len : headLen 6 a r 10=n+1 := by unfold n headLen;omega
  have base : chain D U w n≤treePlus A d 9 := le_sup_right.trans (le_of_eq e9.symm)
  have old := (chain_le_iff n).mp base
  have hn : (D^n) w∉treePlus A d 9 := by
    intro h
    have cb : Band13 A a r U w 10≤treePlus A d 9 := by
      unfold Band13 forwardBand
      rw [len]
      exact sup_le base ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have ff : treePlus A d 10≤treePlus A d 9 := by
      rw [e10]
      exact sup_le (le_sup_left.trans (le_of_eq e9.symm)) cb
    have rk:=Submodule.finrank_mono ff
    omega
  have ct:=more_sites_than_paid old.2 hn
  omega

end RKCert.Paired.FiniteMidpoint

