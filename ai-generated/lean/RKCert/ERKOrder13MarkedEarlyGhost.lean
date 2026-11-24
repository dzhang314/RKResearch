module
public import RKCert.ERKOrder13MarkedFeatureCapacity
public import RKCert.ERKOrder13MarkedGhostScalar
public import RKCert.ERKOrder13TerminalMoments

@[expose] public section
/-! # End-to-end early marked rank-two genuine-ghost exclusion -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve RKCert.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G H:K[X]}
set_option maxHeartbeats 3800000

theorem marked13_early_clean_ghost_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (rank4:finrank K (zeroSpace A 4)=4) (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (early:(terminal s:Vec K (s+1))∈treeSpace A 7)
    (hd:H.natDegree≤a) (hn:H≠0) (hform:MarkGhost13 H a)
    (ghost:w*w-evalNodes A H∈Band13 A a 2 U w 8) : False := by
  classical
  have wa:=C.width
  have ta: nodes A (Fin.last s)=1 := M.atOne (by decide)
  have end0 (x:Vec K (s+1)) (hx:x∈zeroSpace A 4) : x (Fin.last s)=0 :=
    actual_terminal_vanishes ho S.lastLive (by decide) early hx
  have wLast:w (Fin.last s)=0 := by
    apply dis
    refine ⟨terminal s,marked13_terminal_in_core C ?_,?_⟩
    · rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)]
      exact Submodule.mem_span_singleton_self _
    · rw [terminal_at_last];exact one_ne_zero
  have f4 := marked13_four_exact ho S M C.marked rank4
  have up:U≤defectPlus A 1 4 := by rw [f4];exact ((chain_le_iff _).mp le_rfl).1
  have wPaid:w∈zeroSpace A 4 := by
    apply ordinary_when_augmented_terminal_zero end0 _ wLast
    rw [f4]
    simpa only [pow_zero,one_apply_eq_self] using
      ((chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mp le_rfl).2 0 (by decide)
  have gm : (0:Vec K (s+1))-evalNodes A G∈chain (diag (nodes A)) U w 4 := by
    rw [zero_sub,show chain (diag (nodes A)) U w 4=firstEscape A 1 6 from C.marked.edge.symm]
    exact Submodule.neg_mem _ C.meshPaid
  have G_lift := terminal_lift_from_paid_head (P:=G) (j:=7) (n:=4) ho ta up end0 wPaid wLast
    ((zeroSpace A 7).zero_mem) (by rfl) (by decide) (by decide) (by decide) (by decide) gm
  have gm0:scalarMoment G 0=G.eval 1*b (Fin.last s) :=
    terminal_scalar_moment ho (by have:=C.meshDegree;omega) (by decide) G_lift
  let n:=headLen 6 a 2 8
  have nr : 5≤n∧n≤6 := by dsimp [n,headLen];omega
  have z8 : w*w∈zeroSpace A 8 := zeroSpace_mul (m:=4) (n:=4) wPaid wPaid
  have zp : w*w∈zeroSpace A (n+3) := zeroSpace_mono A (by omega) z8
  have H_lift := terminal_lift_from_paid_head (P:=H) (j:=n+3) (n:=n) ho ta up end0 wPaid wLast
    zp (by simp [wLast]) (by omega) le_rfl (by omega) (by omega) ghost
  have hm0:scalarMoment H 0=H.eval 1*b (Fin.last s) :=
    terminal_scalar_moment ho (by omega) (by omega) H_lift
  apply marked13_ghost_feature_contradiction ha ho S M C alg dis ghost
  intro Q R qd rd hSites
  rcases (show a=6∨a=5 by omega) with rfl|rfl
  · cases hform with
    | unaliased h4 h5 he =>
      cases C.mesh with
      | marked g5 g6 ge =>
        have g6n:g6≠0 := by
          intro zero
          have gg := C.meshDegree
          rw [ge,zero,zero_smul,add_zero] at gg
          have gl := natDegree_smul_le g5 (dx5:K[X])
          rw [dx5_degree] at gl
          omega
        let p6:K:=56*g6
        let p5:K:=42*g5
        let h5':K:=42*h5
        let h4':K:=30*h4
        let P:=Polynomial.C p6*dSixPoly+Polynomial.C p5*dFivePoly
        let T:=Polynomial.C h5'*dFivePoly+Polynomial.C h4'*markD4
        have p6n:p6≠0 := mul_ne_zero (by norm_num) g6n
        have gp:G=X*P := by
          rw [ge,dx5_mark_factor,dx6_as_dSix,←Nat.cast_smul_eq_nsmul K (56:ℕ) (X*dSixPoly:K[X])]
          simp only [P,p6,p5,smul_eq_C_mul,map_mul]
          norm_num
          ring
        have hp:H=X*T := by
          rw [he,dx4_mark_factor,dx5_mark_factor]
          simp only [T,h5',h4',smul_eq_C_mul,map_mul]
          ring
        have hnon:h5'≠0∨h4'≠0 := by
          by_contra! e
          apply hn
          simp [hp,T,e.1,e.2]
        have gm: p6/56+p5/42=b (Fin.last s)*(p6+p5) := by
          have x : scalarMoment G 0=g5+g6 := by
            rw [ge,scalarMoment_zero_grade_add,scalarMoment_zero_grade_scale,scalarMoment_zero_grade_scale,
              dx5_scalarMoment0,dx6_scalarMoment0,mul_one,mul_one]
          have y : G.eval 1=p6+p5 := by rw [gp];norm_num [P,dSixValue,dFive]
          rw [x,y] at gm0
          dsimp [p6,p5]
          linear_combination gm0
        have hm: h5'/42+h4'/30=b (Fin.last s)*(h5'+h4') := by
          have x : scalarMoment H 0=h4+h5 := by
            rw [he,scalarMoment_zero_grade_add,scalarMoment_zero_grade_scale,scalarMoment_zero_grade_scale,
              dx4_scalarMoment0,dx5_scalarMoment0,mul_one,mul_one]
          have y : H.eval 1=h5'+h4' := by rw [hp];norm_num [T,dFive,markD4]
          rw [x,y] at hm0
          dsimp [h5',h4']
          linear_combination hm0
        have co:IsCoprime P T:=marked_noalias_early_coprime _ _ _ _ _ p6n hnon gm hm
        have pn : P≠0 := by
          intro z
          have d:=C.meshDegree
          rw [gp,z,mul_zero,natDegree_zero] at d
          omega
        have fdeg : (X*P).natDegree=7 := by rw [←gp,C.meshDegree]
        have bound := marked_eliminant_capacity P T Q R pn co
          (fun qn=>marked_noalias_pencil_not_square_divisor p6n qn qd)
          (by omega) (by rwa [←hp]) qd (by change R.natDegree<5 at rd;omega)
          (headFeatures (nodes A) w) (by rwa [←gp,←hp])
        rwa [←gp,←hp] at bound
  · obtain ⟨g5,ge⟩:=marked13_alias_mesh C
    cases hform with
    | aliased h3 h4 he =>
      let p5 : K := 42*g5
      let h4' : K := 30*h4
      let h3' : K := 20*h3
      let P := Polynomial.C p5*(dFivePoly:K[X])
      let T := Polynomial.C h4'*markD4+Polynomial.C h3'*markD3
      have g5n:g5≠0 := by
        intro zero
        have d:=C.meshDegree
        rw [ge,zero,zero_smul,natDegree_zero] at d
        omega
      have p5n:p5≠0 := mul_ne_zero (by norm_num) g5n
      have gp:G=X*P := by
        rw [ge,dx5_mark_factor]
        simp only [P,p5,smul_eq_C_mul,map_mul]
        ring
      have hp:H=X*T := by
        rw [he,dx3_mark_factor,dx4_mark_factor]
        simp only [T,h4',h3',smul_eq_C_mul,map_mul]
        ring
      have hnon:h4'≠0∨h3'≠0 := by
        by_contra! e
        apply hn
        simp [hp,T,e.1,e.2]
      have gm:p5/42=b (Fin.last s)*p5 := by
        have x : scalarMoment G 0=g5 := by rw [ge,scalarMoment_zero_grade_scale,dx5_scalarMoment0,mul_one]
        have y : G.eval 1=p5 := by rw [gp];norm_num [P,dFive]
        rw [x,y] at gm0
        dsimp [p5]
        linear_combination gm0
      have hm:h4'/30+h3'/20=b (Fin.last s)*(h4'+h3') := by
        have x : scalarMoment H 0=h3+h4 := by
          rw [he,scalarMoment_zero_grade_add,scalarMoment_zero_grade_scale,scalarMoment_zero_grade_scale,
            dx3_scalarMoment0,dx4_scalarMoment0,mul_one,mul_one]
        have y : H.eval 1=h4'+h3' := by rw [hp];norm_num [T,markD4,markD3]
        rw [x,y] at hm0
        dsimp [h4',h3']
        linear_combination hm0
      have co:IsCoprime P T:=marked_alias_early_coprime _ _ _ _ p5n hnon gm hm
      have pn : P≠0 := by
        intro z
        have d:=C.meshDegree
        rw [gp,z,mul_zero,natDegree_zero] at d
        omega
      have fdeg : (X*P).natDegree=6 := by rw [←gp,C.meshDegree]
      have noDiv (qn:Q≠0) : ¬P∣Q^2 := by
        intro h
        have dp : (dFivePoly:K[X])∣P := dvd_mul_left .. 
        have aq := ((mark_d5_separable (K:=K)).squarefree.dvd_pow_iff_dvd (n:=2) (by decide)).mp (dp.trans h)
        have d:=natDegree_le_of_dvd aq qn
        rw [natDegree_dFivePoly] at d
        omega
      have bound := marked_eliminant_capacity P T Q R pn co noDiv
        (by omega) (by rw [←hp];omega) qd (by change R.natDegree<6 at rd;omega)
        (headFeatures (nodes A) w) (by rwa [←gp,←hp])
      rwa [←gp,←hp] at bound

end RKCert.Paired.FiniteMidpoint
