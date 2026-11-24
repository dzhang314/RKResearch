module
public import RKCert.ERKOrder13OddGhost
public import RKCert.ERKOrder13FirstLeak
public import RKCert.OrderTwelveCoreRows

@[expose] public section
/-! # Actual full-odd head features, allowing distinct values at equal clocks -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2000000

theorem full13_mesh_profile (C:Chart13 A 0 6 2 U w G) :
    ∃ a:K,a≠0 ∧ G=a•(X*oddSixPoly) := by
  cases C.mesh with
  | full a e =>
    refine ⟨a,?_,by rw [e,odd6_as_oddSix]⟩
    intro hz
    have h:=C.meshDegree
    rw [e,hz,zero_smul,natDegree_zero] at h
    omega

theorem full13_mesh_heads (C:Chart13 A 0 6 2 U w G) :
    ∃ Q:K[X], Q.natDegree≤3 ∧ ∃ u∈U,
      ∀ i,G.eval (nodes A i)=u i+Q.eval (nodes A i)*w i := by
  have e : evalNodes A G∈chain (diag (nodes A)) U w (2+(6-4)) := by
    rw [←C.marked.edge];exact C.meshPaid
  obtain ⟨u,hu,Q,hd,he⟩:=exists_head_poly e
  have de:Q.natDegree≤3 := by
    by_cases q0:Q=0
    · simp [q0]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt q0).mpr hd)
  refine ⟨Q,de,u,hu,fun i=>?_⟩
  simpa only [evalNodes_apply] using he i

theorem full13_ghost_coprime {α:K} (hα:α≠0) :
    IsCoprime (oddSixPoly:K[X]) (α•odd5) := by
  obtain ⟨u,v,e⟩ := oddSix_ghost_coprime (K:=K)
  refine ⟨u,v*Polynomial.C α⁻¹,?_⟩
  rw [smul_eq_C_mul]
  have hh : Polynomial.C α⁻¹*Polynomial.C α=(1:K[X]) := by
    rw [←map_mul,inv_mul_cancel₀ hα,map_one]
  linear_combination v*odd5*hh+e

theorem full13_ghost_head_capacity (F H Q R:K[X]) (fd:F.natDegree=7)
    (hd:H.natDegree≤6) (qd:Q.natDegree≤3) (rd:R.natDegree≤4)
    (f0:F.eval 0=0) (h0:H.eval 0=0)
    (fD:(oddSixPoly:K[X])∣F) (co:IsCoprime (oddSixPoly:K[X]) H)
    (S:Finset (K×K))
    (hS:∀ w∈S,w.2≠0 ∧ F.eval w.1=w.2*Q.eval w.1 ∧
      w.2^2=H.eval w.1+w.2*R.eval w.1) : S.card≤13 := by
  classical
  let P:=F^2-F*Q*R-H*Q^2
  have fn:F≠0 := by intro hz;rw [hz,natDegree_zero] at fd;omega
  have pn : P≠0 := by
    intro hz
    by_cases qn:Q=0
    · exact pow_ne_zero 2 fn (by simpa [P,qn] using hz)
    · have eq : F^2-F*Q*R=H*Q^2 := sub_eq_zero.mp hz
      have hD : (oddSixPoly:K[X])∣F^2-F*Q*R := by
        exact dvd_sub (fD.trans (dvd_pow_self _ (by decide))) ((fD.trans (dvd_mul_right F Q)).trans
          (dvd_mul_right (F*Q) R))
      rw [eq,mul_comm] at hD
      have hq := co.dvd_of_dvd_mul_right hD
      have divQ := ((oddSix_separable (K:=K)).squarefree.dvd_pow_iff_dvd (n:=2) (by decide)).mp hq
      have hh := natDegree_le_of_dvd divQ qn
      rw [oddSixPoly_degree] at hh
      omega
  have pDeg : P.natDegree≤14 := by
    unfold P
    apply le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · apply le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · rw [natDegree_pow,fd]
      · have u := natDegree_mul_le (p:=F*Q) (q:=R)
        have v := natDegree_mul_le (p:=F) (q:=Q)
        omega
    · have g:= natDegree_mul_le (p:=H) (q:=Q^2)
      rw [natDegree_pow] at g
      omega
  have hc:=FeatureCapacity.count_by_eliminant S F H Q R f0 h0 pn hS
  change S.card+1≤P.natDegree at hc
  omega

theorem full13_genuine_ghost_features (C:Chart13 A 0 6 2 U w G)
    (dis:∀ i,Live U i→w i=0) {α:K} (hα:α≠0)
    (hg:w*w-evalNodes A (α•odd5)∈Band13 A 6 2 U w 8) :
    (headFeatures (nodes A) w).card≤13 ∧ (offFeatures U (nodes A) w).card≤1 := by
  classical
  let c:=nodes A
  let H :K[X]:=α•odd5
  have h0:H.eval 0=0 := by rw [show H=α•odd5 from rfl,eval_smul,odd5_as_poly];simp
  have hd : H.natDegree≤6 := (natDegree_smul_le ..).trans (le_of_eq (odd5_degree (K:=K)))
  obtain ⟨a,an,hG⟩:=full13_mesh_profile C
  have fD:(oddSixPoly:K[X])∣G := by
    use Polynomial.C a*X
    rw [hG,smul_eq_C_mul]
    ring
  have f0:G.eval 0=0 := by rw [hG,eval_smul,eval_mul,eval_X,zero_mul,smul_zero]
  have cop:IsCoprime (oddSixPoly:K[X]) H := full13_ghost_coprime hα
  obtain ⟨Q,qd,u,hu,eq⟩:=full13_mesh_heads C
  obtain ⟨v,hv,R,rd,eqR⟩:=exists_head_poly hg
  have dr : R.natDegree≤4 := by
    by_cases h:R=0
    · simp [h]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt h).mpr rd)
  have nz (j:Fin (s+1)) (hj:¬Live U j) (z:Vec K (s+1)) (hz:z∈U) : z j=0 := by
    by_contra hn;exact hj ⟨z,hz,hn⟩
  have second (j:Fin (s+1)) (hj:¬Live U j) : (w j)^2=H.eval (c j)+w j*R.eval (c j) := by
    have hh:=eqR j
    change w j*w j-H.eval (c j)=v j+R.eval (c j)*w j at hh
    rw [nz _ hj _ hv,zero_add] at hh
    linear_combination hh
  constructor
  · apply full13_ghost_head_capacity G H Q R C.meshDegree hd qd dr f0 h0 fD cop
    intro x hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    have hwj: w j≠0 := (Finset.mem_filter.mp hj).2
    have ople : ¬Live U j := fun h=>hwj (dis j h)
    refine ⟨hwj,?_,second j ople⟩
    simpa only [nz _ ople _ hu,zero_add,mul_comm] using eq j
  · apply (Finset.card_le_card (t:=({0}:Finset K)) ?_).trans (by simp)
    intro x hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨bu,bw⟩:=(Finset.mem_filter.mp hj).2
    have hMesh : G.eval (c j)=0 := by
      simpa only [nz _ bu _ hu,bw,mul_zero,zero_add] using eq j
    have gGhost : H.eval (c j)=0 := by
      have hh:=second j bu
      simpa only [bw,zero_pow (by decide : 2≠0),zero_mul,add_zero,eq_comm] using hh
    by_contra h
    have nn : c j≠0 := by simpa only [Finset.mem_singleton] using h
    have d0 : (oddSixPoly:K[X]).eval (c j)=0 := by
      rw [hG,eval_smul,smul_eq_mul,eval_mul,eval_X] at hMesh
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hMesh).resolve_left an)).resolve_left nn
    obtain ⟨P,Q,e⟩:=cop
    have ev:=congrArg (fun L:K[X]=>L.eval (c j)) e
    simp only [eval_add,eval_mul,d0,gGhost,mul_zero,add_zero,eval_one] at ev
    exact zero_ne_one ev

end RKCert.Paired.FiniteMidpoint
