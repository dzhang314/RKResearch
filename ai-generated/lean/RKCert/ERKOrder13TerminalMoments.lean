module
public import RKCert.ERKOrder13LateLift
public import RKCert.ERKOrder13MarkedJacobi

@[expose] public section
/-! # Exact terminal-normalized mesh and ghost moments
These formulas recover the coefficient of the physical terminal coordinate
from the paid ordinary lifts; the coefficient is not inferred from the
augmented rank budget alone. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s j n k:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w z:Vec K (s+1)} {P:K[X]}
set_option maxHeartbeats 3000000

theorem terminal_lift_from_paid_head (ho:HasTreeOrderAtLeast A b 13)
    (atOne:nodes A (Fin.last s)=1)
    (UGrade:U≤defectPlus A 1 k)
    (Uv:∀ x∈zeroSpace A k,x (Fin.last s)=0)
    (h4:w∈zeroSpace A 4) (we:w (Fin.last s)=0)
    (zpaid:z∈zeroSpace A j) (ze:z (Fin.last s)=0)
    (npos:0<n) (budget:n+3≤j) (kk:k≤j) (jp:j≤12)
    (fit:z-evalNodes A P∈chain (diag (nodes A)) U w n) :
    evalNodes A P-P.eval 1 • (terminal s:Vec K (s+1))∈zeroSpace A j := by
  classical
  obtain ⟨u,hu,Q,Qd,hFit⟩:=exists_head_poly fit
  obtain ⟨u0,hu0,v,hv,ueq⟩:=Submodule.mem_sup.mp (UGrade hu)
  rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)] at hv
  obtain ⟨t,rfl⟩:=Submodule.mem_span_singleton.mp hv
  have dq:Q.natDegree<n := by
    by_cases qn:Q=0
    · simp [qn,npos]
    · exact (natDegree_lt_iff_degree_lt qn).mpr Qd
  have qpay : weightedEval (nodes A) w Q∈zeroSpace A j :=
    weighted_thirteen_ordinary ho h4 Q (by omega) (by omega)
  have join : z-evalNodes A P=u0+t • terminal s+weightedEval (nodes A) w Q := by
    ext i
    rw [←ueq] at hFit
    simpa only [Pi.add_apply,weightedEval_apply] using hFit i
  have tval : -(P.eval 1)=t := by
    have h:=congrFun join (Fin.last s)
    simp [evalNodes,ze,Uv u0 hu0,atOne,terminal_at_last,we,weightedEval_apply] at h
    exact h
  have y : z-u0-weightedEval (nodes A) w Q∈zeroSpace A j :=
    (zeroSpace A j).sub_mem ((zeroSpace A j).sub_mem zpaid (zeroSpace_mono A kk hu0)) qpay
  have eq : evalNodes A P-P.eval 1 • (terminal s:Vec K (s+1))=
      z-u0-weightedEval (nodes A) w Q := by
    rw [show evalNodes A P=z-(u0+t • terminal s+weightedEval (nodes A) w Q) by rw [←join];abel,
      ←tval,neg_smul]
    abel
  rwa [eq]

theorem terminal_scalar_moment (ho:HasTreeOrderAtLeast A b 13)
    (pd:P.natDegree≤12) (jt:j≤12)
    (lift:evalNodes A P-P.eval 1 • (terminal s:Vec K (s+1))∈zeroSpace A j) :
    scalarMoment P 0=P.eval 1*b (Fin.last s) := by
  have h:=probe_zeroSpace ho (k:=0) (by omega) lift
  change probe A b 0 (evalNodes A P-P.eval 1 • (terminal s:Vec K (s+1)))=0 at h
  have pr : probe A b 0 (terminal s)=row b (terminal s) := by simp [probe,row_apply]
  rw [map_sub,map_smul,smul_eq_mul,probe_eval_moment ho P 0 (by omega),pr,row_terminal] at h
  exact sub_eq_zero.mp h

theorem scalarMoment_zero_grade_add (P Q:K[X]) :
    scalarMoment (P+Q) 0=scalarMoment P 0+scalarMoment Q 0 := by
  simp [scalarMoment,map_add,eval_add]

theorem scalarMoment_zero_grade_scale (a:K) (P:K[X]) :
    scalarMoment (a • P) 0=a*scalarMoment P 0 := by
  simp [scalarMoment,map_smul,eval_smul]

theorem dx3_scalarMoment0 : scalarMoment (dx3:K[X]) 0=1 := by
  have coef : (fun i:Fin 11=>(dx3:K[X]).coeff i.val)=![0, -20, 180, -420, 280, 0, 0, 0, 0, 0, 0] := by
    ext i
    exact dx3_coeff _ i.isLt
  rw [scalarMoment_11 _ (by rw [dx3_degree];decide),coef]
  norm_num [moment,Fin.sum_univ_succ]

theorem dx4_scalarMoment0 : scalarMoment (dx4:K[X]) 0=1 := by
  have coef : (fun i:Fin 11=>(dx4:K[X]).coeff i.val)=![0, 30, -420, 1680, -2520, 1260, 0, 0, 0, 0, 0] := by
    ext i
    exact dx4_coeff _ i.isLt
  rw [scalarMoment_11 _ (by rw [dx4_degree];decide),coef]
  norm_num [moment,Fin.sum_univ_succ]

theorem dx5_scalarMoment0 : scalarMoment (dx5:K[X]) 0=1 := by
  have coef : (fun i:Fin 11=>(dx5:K[X]).coeff i.val)=![0, -42, 840, -5040, 12600, -13860, 5544, 0, 0, 0, 0] := by
    ext i
    exact dx5_coeff _ i.isLt
  rw [scalarMoment_11 _ (by rw [dx5_degree];decide),coef]
  norm_num [moment,Fin.sum_univ_succ]

theorem dx6_scalarMoment0 : scalarMoment (dx6:K[X]) 0=1 := by
  have coef : (fun i:Fin 11=>(dx6:K[X]).coeff i.val)=![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0] := by
    ext i
    exact dx6_coeff _ i.isLt
  rw [scalarMoment_11 _ (by rw [dx6_degree];decide),coef]
  norm_num [moment,Fin.sum_univ_succ]

end RKCert.Paired.FiniteMidpoint
