module
public import RKCert.DirkTwentyTenZero
public import RKCert.EndpointTailMoments
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial Module RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s p m:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
noncomputable section
/-- One clean right endpoint replaces one missing scalar moment. This
proof differentiates x^{j+1}P and applies an x-weighted Hilbert detector
to P', so no order on K or identity of a chosen orthogonal polynomial
is needed. -/
theorem right_moment_separates (P:K[X]) {m:ℕ} (pos:0<m) (degree:P.natDegree≤m)
    (one:P.eval 1=0) (mom:∀k<m,integral (X^k*P)=0):P=0:=by
  have derivative (k:ℕ)(pay:k<m):integral (X^(k+1)*P.derivative)=0:=by
    let T:=X^(k+1)*P
    have t0:T.coeff 0=0:=by simp [T,coeff_zero_eq_eval_zero]
    have t1:T.eval 1=0:=by simp [T,one]
    have dt:integral T.derivative=0:=by rw [integral_eq,primitive_derivative T t0,t1]
    have rule:T.derivative=((k+1:ℕ):K) • (X^k*P)+X^(k+1)*P.derivative:=by
      simp [T,derivative_mul,derivative_X_pow_succ,smul_eq_C_mul,mul_assoc]
    rw [rule,map_add,map_smul,smul_eq_mul,mom k pay,mul_zero,zero_add] at dt
    exact dt
  have dp:P.derivative=0:=primitive_shift_detect P.derivative (k:=1)
    ((natDegree_derivative_le P).trans (Nat.sub_le_sub_right degree 1)) 1 one_ne_zero (fun i=>by
      have paid:i.val<m:=by have:=i.isLt;omega
      have e:=derivative i.val paid
      simpa only [integral_eq,formalPrimitive_eq_treePrimitive,Nat.add_comm 1 i.val] using e)
  have con:=eq_C_of_derivative_eq_zero dp
  have e:=congrArg (fun F:K[X]=>F.eval 1) con
  change P.eval 1=(C (P.coeff 0)).eval 1 at e
  rw [one,eval_C] at e
  exact con.trans (by rw [←e,C_0])

theorem scalar_separation_of_clean_one (ho:HasTreeOrderAtLeast A b p) (pos:0<m) (pay:2*m≤p)
    (t:Fin s) (ct:nodes A t=1) (clean:∀f∈zeroSpace A m,f t=0):Separated A m:=by
  intro P dP hv
  have p1:=clean _ hv
  rw [evalNodes_apply,ct] at p1
  apply right_moment_separates P pos dP p1
  intro k small
  have pure:probe A b k (evalNodes A P)=0:=probe_zeroSpace ho (by omega) hv
  rw [(OrdinaryTrace.scalar A dP).probe ho k (by omega),formalPrimitive_eq_treePrimitive] at pure
  exact pure

variable {T:Fin (s+1)→Fin (s+1)→K} {β:Vec K (s+1)}
/-- The complete physical grade-ten terminal-zero result forces the
anchored C(2) branch. In particular, F5 has rank 3 or 4, F6 at least 5,
F10 exactly 10, and F11 at most 12. -/
theorem twenty_origin (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β 20) (size:s+1=28) :
    TwentyRanks T β 0 ∧ (∀j,T 0 j=0) ∧ ∀f∈zeroSpace T 10,f (Fin.last s)=0:=by
  obtain ⟨e,h⟩:=twenty_ranks ha ho size
  have clean:=twenty_all_ten_zero ha ho size
  obtain ⟨_,ct,_⟩:=twenty_final_row ha ho size h
  have sep:=scalar_separation_of_clean_one ho (by decide:0<10) (by decide) (Fin.last s) ct clean
  have rank:=treeSpace_rank_of_separated T 10 ((separated_iff_coeff T 10).mp sep)
  have cap:finrank K (treeSpace T 10)=21:=(h.dual 10 7 (by decide) (by decide)).1
  have ten:=h.ten
  have zero:e=0:=by omega
  subst e
  have c2:q₂ (mat T) (nodes T) 1=0:=by rcases h.flag with ⟨_,eqn⟩|⟨bad,_⟩;exact eqn;omega
  exact ⟨h,dirk_first_row ha c2,clean⟩
end
end RKCert.Paired.Terminal

