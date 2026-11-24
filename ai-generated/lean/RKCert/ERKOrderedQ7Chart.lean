module
public import RKCert.ERKShortMidpoint
public import RKCert.ERKOrderedQ7Shifts
public import RKCert.ERKFiniteCore

@[expose] public section

/-! # Exact even order-14 midpoint and ordinary one-head bands -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 1300000

noncomputable abbrev SevenBand (A:Fin (s+1)→Fin (s+1)→K) (r:ℕ) (U:Submodule K (Vec K (s+1)))
    (w:Vec K (s+1)) (j:ℕ) := forwardBand A 7 7 r U w j

structure EvenSevenChart (A:Fin (s+1)→Fin (s+1)→K) (r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (G:K[X]) : Prop where
  marked : MarkedHead A 7 0 r U w
  mesh : ∃ t:K,G=t•even6
  meshDegree : G.natDegree=8
  meshPaid : evalNodes A G∈firstEscape A 0 7
  chart : ∀ j,8≤j→j≤11→treePlus A 0 j=polyBand A 7⊔SevenBand A r U w j
  rich : ∀ j,8≤j→j≤11→finrank K (treePlus A 0 j)=j+8

omit [CharZero K] in
theorem even_seven_margin (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) : Margin A b 7 0 0 := by
  simpa only [Nat.zero_sub] using margin_short (q:=7) (ε:=0) ha ho (by decide) (by decide) S

theorem even_seven_mesh (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (P:K[X]) (pd:P.natDegree≤8)
    (hP:evalNodes A P∈firstEscape A 0 7) : ∃ t:K,P=t•even6 := by
  have hs : s≠0 := by have :=S.size;omega
  have h0 := marked_eval_origin ha hs P (firstEscape_defect hP)
  have hlast := firstEscape_last_zero_short (q:=7) ha ho (by decide) S hP
  have one := (even_terminal_column_short (q:=7) ha ho (by decide) S).1
  have h1 : P.eval 1=0 := by simpa only [evalNodes_apply,one] using hlast
  exact meshEven7_decode P pd h0 h1 (fun k=>marked_moment_zero ho P (firstEscape_defect hP) pd (by have:=k.isLt;omega))

theorem even_seven_chart (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (M:Margin A b 7 0 0) :
    ∃ r U w G,EvenSevenChart A r U w G := by
  have ho' : HasTreeOrderAtLeast A b (2*7+0) := ho
  obtain ⟨r,U,w,H⟩:=marked_head_short ha ho' (by decide) (by decide) S M
  have sep (P:K[X]) (hd:P.natDegree≤7) (hP:evalNodes A P∈firstEscape A 0 7) : P=0 := by
    by_contra hn
    obtain ⟨t,h⟩:=even_seven_mesh ha ho S P (by omega) hP
    have e := (mesh_line_degree h hn).trans even6_degree
    omega
  obtain ⟨eq,rr,G,gd,gp⟩:=band_start_noalias_short ho' (by decide) M H sep
  have e : treePlus A 0 8=polyBand A 7⊔chain (diag (nodes A)) U w (r+3) := by
    rwa [←H.edge]
  have prev : finrank K (treePlus A 0 (8-1))=(if (8:ℕ)=7 then 2*7-1+0 else 7+8+0) := by
    have := M.eMid
    simpa using this
  have stairs := band_staircase_short (q:=7) (ε:=0) (d:=0) (a:=7) (l:=r+3)
    ha ho' (by decide) M (by decide) (by omega) H.stable e (by simpa using rr) prev
  have all (j:ℕ) (jl:8≤j) (ju:j≤11) :
      treePlus A 0 j=polyBand A 7⊔SevenBand A r U w j ∧
      finrank K (treePlus A 0 j)=j+8 := by
    have h:=stairs (j-8) (by omega)
    rw [show 7+1+(j-8)=j by omega] at h
    exact ⟨h.1,by omega⟩
  exact ⟨r,U,w,G,⟨H,even_seven_mesh ha ho S G gd.le gp,gd,gp,
    fun j jl ju=>(all j jl ju).1,fun j jl ju=>(all j jl ju).2⟩⟩

omit [CharZero K] in
theorem even_seven_next (C:EvenSevenChart A r U w G) {j:ℕ} (hj:8≤j) :
    SevenBand A r U w j ⊔ (SevenBand A r U w j).map (diag (nodes A))=SevenBand A r U w (j+1) := by
  have eq : headLen 7 7 r (j+1)=headLen 7 7 r j+1 := by unfold headLen;omega
  unfold SevenBand forwardBand
  rw [eq]
  exact chain_sup_map C.marked.stable (by unfold headLen;omega)

omit [CharZero K] in
theorem even_seven_first (C:EvenSevenChart A r U w G) {j:ℕ} :
    firstEscape A 0 7≤SevenBand A r U w j := by
  rw [C.marked.edge]
  unfold SevenBand forwardBand headLen
  have h := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+3+(j-8))).mp le_rfl
  exact (chain_le_iff _).mpr ⟨h.1,fun k hk=>h.2 k (by omega)⟩

omit [CharZero K] in
theorem even_seven_paid (C:EvenSevenChart A r U w G) (j:ℕ) :
    SevenBand A r U w (8+j)≤defectPlus A 0 (8+j) := by
  induction j with
  | zero =>
    change chain (diag (nodes A)) U w (r+3)≤defectPlus A 0 8
    rw [←C.marked.edge]
    exact firstEscape_defect
  | succ j ih =>
    rw [show 8+(j+1)=8+j+1 by omega,←even_seven_next C (by omega)]
    exact sup_le (ih.trans (Fplus_mono A 0 (Nat.le_succ _)))
      ((Submodule.map_mono ih).trans (Fplus_clock A 0 (8+j)))

theorem even_seven_band_zero (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (C:EvenSevenChart A r U w G) (j:ℕ) {z:Vec K (s+1)}
    (hz:z∈SevenBand A r U w j) : z (Fin.last s)=0 := by
  have h5 (v:Vec K (s+1)) (hv:v∈defectPlus A 0 5) : v (Fin.last s)=0 :=
    even_last_zero_short ha ho (by decide) S _ (zeroSpace_mono A (by decide) (tail_zero_iff.mp hv))
  have w5 : w∈defectPlus A 0 5 := by
    simpa using marked_power C.marked (by decide) (k:=0) (by have := C.marked.rTwo;omega)
  exact chain_eval_zero _ (fun v hv=>h5 v (C.marked.core hv)) (h5 _ w5) hz

omit [CharZero K] in
theorem even_seven_band_sep (S:Saturated A b 7 0) (M:Margin A b 7 0 0)
    (C:EvenSevenChart A r U w G) {j:ℕ} (j0:8≤j) (j1:j≤11)
    (P:K[X]) (hp:P.natDegree≤7) (hm:evalNodes A P∈SevenBand A r U w j) : P=0 := by
  have inj : Function.Injective (polyEval A 7) := (injective_iff_map_eq_zero _).mpr fun t ht=>by
    have h:=evalNodes_ofFn A 7 t
    have hd : (ofFn 8 t).natDegree≤7 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    have e : ofFn 8 t=0 :=
      separated_plus S M _ hd (by rw [h,ht];exact (defectPlus A 0 7).zero_mem)
    ext i
    have ee:=congrArg (fun P:K[X]=>P.coeff i.val) e
    rwa [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] at ee
  have pRank : finrank K (polyBand A 7)=8 := by unfold polyBand;rw [LinearMap.finrank_range_of_inj inj];simp
  let Z:=SevenBand A r U w j
  have cap : finrank K Z≤finrank K U+headLen 7 7 r j := RKCert.Paired.OrderTwelve.chain_rank_cap _
  have sum := Submodule.finrank_sup_add_finrank_inf_eq (polyBand A 7) Z
  have eq := C.chart j j0 j1
  change treePlus A 0 j=polyBand A 7⊔Z at eq
  rw [←eq,C.rich j j0 j1,pRank] at sum
  have rz : finrank K ↥(polyBand A 7⊓Z)=0 := by
    have := C.marked.rank
    unfold headLen at cap
    omega
  have hbot := Submodule.finrank_eq_zero.mp rz
  have z : evalNodes A P=0 := (Submodule.mem_bot K).mp (hbot ▸ Submodule.mem_inf.mpr ⟨eval_polyBand hp,hm⟩)
  exact separated_plus S M P hp (by rw [z];exact (defectPlus A 0 7).zero_mem)

omit [CharZero K] in
theorem even_seven_sites (C:EvenSevenChart A r U w G) :
    r+6≤(headSites (nodes A) w).card := by
  let D:=diag (nodes A)
  have e10 : treePlus A 0 10=polyBand A 7⊔chain D U w (r+5) := by
    have e : headLen 7 7 r 10=r+5 := by unfold headLen;omega
    simpa only [SevenBand,forwardBand,e] using C.chart 10 (by decide) (by decide)
  have e11 : treePlus A 0 11=polyBand A 7⊔chain D U w (r+5+1) := by
    have e : headLen 7 7 r 11=r+5+1 := by unfold headLen;omega
    simpa only [SevenBand,forwardBand,e] using C.chart 11 (by decide) (by decide)
  have base : chain D U w (r+5)≤treePlus A 0 10 := le_sup_right.trans (le_of_eq e10.symm)
  have old := (chain_le_iff (r+5)).mp base
  have hn : (D^(r+5)) w∉treePlus A 0 10 := by
    intro h
    have hh : treePlus A 0 11≤treePlus A 0 10 := by
      rw [e11]
      exact sup_le (le_sup_left.trans (le_of_eq e10.symm)) (sup_le base ((Submodule.span_singleton_le_iff_mem ..).mpr h))
    have r10:=C.rich 10 (by decide) (by decide)
    have r11:=C.rich 11 (by decide) (by decide)
    have hc:=Submodule.finrank_mono hh
    omega
  have h := more_sites_than_paid old.2 hn
  omega

end RKCert.Paired.FiniteMidpoint

