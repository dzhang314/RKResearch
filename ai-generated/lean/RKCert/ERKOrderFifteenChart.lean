module
public import RKCert.ERKOrderFifteenPackets
public import RKCert.ERKShortMidpoint
public import RKCert.ERKFiniteChart

@[expose] public section

/-! # Actual order-fifteen midpoint, including its unique projected alias

There are only two head meshes: the full x-weighted degree-seven
orthogonal polynomial and the marked x(1−x)-weighted pencil. The only
lower-degree alias is the fixed x times the Lobatto sextic. This
module records actual original-array ranks across the finite horizon,
not hypotheses supplied by a downstream endpoint test.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.OneEscape Polynomial Module
variable {K : Type*} [Field K] [CharZero K] {s d a r : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

inductive OddSevenMesh (P : K[X]) : ℕ → Prop
  | full (t:K) (e : P=t • odd7) : OddSevenMesh P 0
  | marked (t u:K) (e : P=t • dx6+u • dx7) : OddSevenMesh P 1

theorem odd_seven_mesh (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d)
    (P : K[X]) (pd : P.natDegree≤8) (hp : evalNodes A P∈firstEscape A d 7) :
    OddSevenMesh P d := by
  have hs : s≠0 := by have := S.size; omega
  have h0 := marked_eval_origin ha hs P (firstEscape_defect hp)
  have d1 : d≤1 := by have := M.budget; omega
  interval_cases d
  · obtain ⟨t,e⟩ := meshOddFull7_decode P pd h0 (fun k =>
      marked_moment_zero ho P (firstEscape_defect hp) pd (by have := k.isLt; omega))
    exact .full t e
  · obtain ⟨t,u,e⟩ := meshOddPrefix7_decode P pd h0 (fun k =>
      marked_moment_difference ho P (firstEscape_defect hp) pd M.atOne
        (by have := k.isLt; omega))
    exact .marked t u e

theorem odd_seven_alias_form {P : K[X]} (H : OddSevenMesh P d)
    (pd : P.natDegree≤7) (pn : P≠0) :
    d=1 ∧ P.natDegree=7 ∧ ∃ t : K, t≠0 ∧ P=t • dx6 := by
  cases H with
  | full t e =>
    have eq := (mesh_line_degree e pn).trans odd7_degree
    omega
  | marked t u e =>
    have d6 := dx6_degree (K:=K)
    have d7 := dx7_degree (K:=K)
    have hu : u=0 := by
      by_contra nz
      have udeg := natDegree_smul (dx7:K[X]) nz
      have tdeg := natDegree_smul_le t (dx6:K[X])
      have h : (t • (dx6:K[X])).natDegree < (u • (dx7:K[X])).natDegree := by omega
      rw [e,natDegree_add_eq_right_of_natDegree_lt h,udeg,d7] at pd
      omega
    have e' : P=t • dx6 := by simpa only [hu,zero_smul,add_zero] using e
    refine ⟨rfl,(mesh_line_degree e' pn).trans d6,t,?_,e'⟩
    intro z
    apply pn
    rw [e',z,zero_smul]

structure OddSevenChart (A : Fin (s+1)→Fin (s+1)→K) (d a r : ℕ)
    (U : Submodule K (Vec K (s+1))) (w : Vec K (s+1)) (G : K[X]) : Prop where
  marked : MarkedHead A 7 d r U w
  chartType : a=7 ∨ a=6 ∧ d=1
  mesh : OddSevenMesh G d
  meshDegree : G.natDegree=a+1
  meshPaid : evalNodes A G∈firstEscape A d 7
  chart : ∀ j,a+1≤j→j≤12→treePlus A d j=polyBand A a⊔forwardBand A 7 a r U w j
  rich : ∀ j,a+1≤j→j≤12→finrank K (treePlus A d j)=j+8+d

theorem odd_seven_chart (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) :
    ∃ a r U w G, OddSevenChart A d a r U w G := by
  have ho' : HasTreeOrderAtLeast A b (2*7+1) := ho
  obtain ⟨r,U,w,H⟩ := marked_head_short ha ho' (by decide) (by decide) S M
  have finalize (a : ℕ) (ht : a=7 ∨ a=6 ∧ d=1) (G : K[X]) (gd : G.natDegree=a+1)
      (gp : evalNodes A G∈firstEscape A d 7)
      (eq : treePlus A d (a+1)=polyBand A a⊔firstEscape A d 7)
      (rr : finrank K (treePlus A d (a+1))=7+(a+1)+1+d)
      (rp : finrank K (treePlus A d ((a+1)-1))=
        if a+1=7 then 2*7-1+d else 7+(a+1)+d) :
      OddSevenChart A d a r U w G := by
    have aLe : a≤7 := by rcases ht with h|h <;> omega
    have aLo : 7≤a+1 := by rcases ht with h|h <;> omega
    have stairs := band_staircase_short ha ho' (by decide) M aLo
      (show 0<r+(7-4) by omega) H.stable (by rwa [←H.edge]) rr rp
    have all (j:ℕ) (hj:a+1≤j) (hmax:j≤12) :
        treePlus A d j=polyBand A a⊔forwardBand A 7 a r U w j ∧
        finrank K (treePlus A d j)=j+8+d := by
      have hx := stairs (j-(a+1)) (by omega)
      rw [show a+1+(j-(a+1))=j by omega] at hx
      exact ⟨hx.1,by omega⟩
    exact ⟨H,ht,odd_seven_mesh ha ho S M G (by omega) gp,gd,gp,
      fun j hj hm=>(all j hj hm).1,fun j hj hm=>(all j hj hm).2⟩
  by_cases h : ∀ P:K[X],P.natDegree≤7→evalNodes A P∈firstEscape A d 7→P=0
  · obtain ⟨eq,rr,G,gd,gp⟩:=band_start_noalias_short ho' (by decide) M H h
    refine ⟨7,r,U,w,G,finalize 7 (Or.inl rfl) G gd gp eq rr ?_⟩
    simpa using M.eMid
  · push Not at h
    obtain ⟨G,gd,gp,gn⟩:=h
    have hmesh := odd_seven_mesh ha ho S M G (by omega) gp
    obtain ⟨d1,gdeg,_,_,_⟩:=odd_seven_alias_form hmesh gd gn
    have low (P:K[X]) (hd:P.natDegree≤7-1) (hp:evalNodes A P∈firstEscape A d 7) : P=0 := by
      by_contra pn
      have e := (odd_seven_alias_form (odd_seven_mesh ha ho S M P (by omega) hp) (by omega) pn).2.1
      omega
    have eq := band_start_alias_short ho' (by decide) M (by decide) S H low G gdeg gp
    exact ⟨6,r,U,w,G,finalize 6 (Or.inr ⟨rfl,d1⟩) G gdeg gp eq M.eMid M.ePrev⟩

/-- Order fifteen on at most 22 stages forces the actual saturated and
marked midpoint chart, including the full rank budget and admissible mesh. -/
theorem at_order_fifteen (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (sz : s+1≤22) :
    ∃ d a r U w G,Saturated A b 7 1 ∧ Margin A b 7 1 d ∧ OddSevenChart A d a r U w G := by
  have ho' : HasTreeOrderAtLeast A b (2*7+1) := ho
  have S := saturated_short ha ho' (by decide) (by decide) (by omega)
  have M := margin_short ha ho' (by decide) (by decide) S
  obtain ⟨a,r,U,w,G,C⟩ := odd_seven_chart ha ho S M
  exact ⟨_,a,r,U,w,G,S,M,C⟩

end RKCert.Paired.FiniteMidpoint
