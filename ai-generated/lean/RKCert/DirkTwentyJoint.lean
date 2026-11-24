module
public import RKCert.DirkTwentyTerminal
public import RKCert.DirkPaidPorts
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

/-- The marked terminal restriction through nine is earned, not presumed
from the forward terminal-zero alternative at grade ten. -/
theorem twenty_paid_reverse (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    {e:ℕ} (h:TwentyRanks A b e):PaidReverseBand A b 20 9:=by
  obtain ⟨_,ct,col,_,_⟩:=twenty_final_row ha ho size h
  have last(j:Fin (s+1))(later:Fin.last s<j):b j=0:=False.elim ((not_lt_of_ge (Fin.le_last j)) later)
  have y:mirror A (Fin.last s)=0:=by change 1-nodes A _=0;rw [ct,sub_self]
  refine ⟨by decide,by decide,ct,col,h.seeds,?_,?_⟩
  · intro r small
    exact (h.dual (17-r) r (by omega) (by omega)).2.1
  · intro j low hi
    apply le_antisymm
    · intro x hz
      exact h.words j low hi ▸ hz.1
    · intro x hx
      refine ⟨(h.words j low hi).symm ▸ hx,?_⟩
      exact dirkBack_prior ha _ last y h.seeds.1 h.seeds.2 (j-2) hx _ (show Fin.last s≤Fin.last s from le_rfl)

omit [CharZero K] in
/-- A b-invisible vector in a fully spanned scalar/pure grade has no scalar
part when either the unanchored Cauchy probes, or one earned first-row
zero and the remaining probes, exhaust the scalar coefficients. -/
theorem pure_of_weight_zero {p q m:ℕ} (ho:HasTreeOrderAtLeast A b p) (low:q≤m)
    (esc:q+m+1≤p ∨ (q+m≤p ∧ ∀j,A 0 j=0))
    (full:treeSpace A m=LinearMap.range (polyEval A q) ⊔ zeroSpace A m)
    {z:Vec K (s+1)} (mem:z∈treeSpace A m) (wb:b*z=0) (anchor:(∀j,A 0 j=0)→z 0=0 ∨ q+m+1≤p) :z∈zeroSpace A m:=by
  rw [full] at mem
  obtain ⟨_,⟨a,rfl⟩,f,hf,eqn⟩:=Submodule.mem_sup.mp mem
  have probes(k:ℕ):probe A b k z=0:=by
    rw [probe,row_apply];apply Finset.sum_eq_zero
    intro i _
    have bi:b i*z i=0:=congrFun wb i
    calc
      _=(nodes A i)^k*(b i*z i):=by ring
      _=0:=by rw [bi,mul_zero]
  have scalar (k:ℕ)(hk:k+m+1≤p):probe A b k (polyEval A q a)=0:=by
    have eq:=probes k
    rw [←eqn,map_add] at eq
    have pure:probe A b k f=0:=probe_zeroSpace ho hk hf
    rwa [pure,add_zero] at eq
  have non(qpay:q+m+1≤p):a=0:=by
    ext j
    apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l=>by omega) a _ j
    intro k
    have x:=scalar k.val (by omega)
    rwa [probe_polyEval ho (by omega)] at x
  have az:a=0:=by
    rcases esc with ready|⟨pay,org⟩
    · exact non ready
    rcases anchor org with z0|ready
    · have c0:a 0=0:=by
        have e:=congrFun eqn (0:Fin (s+1))
        have f0:f 0=0:=zeroSpace_first_of_row org m hf
        simpa only [Pi.add_apply,polyEval_first_of_row org,f0,add_zero,z0] using e
      have ker(i:Fin q): (∑j:Fin q,a j.succ/((i.val+j.val+2:ℕ):K))=0:=by
        have p0:=scalar i.val (by omega)
        rw [probe_polyEval ho (by omega),Fin.sum_univ_succ,c0,zero_div,zero_add] at p0
        simpa only [Fin.val_succ,Nat.add_assoc] using p0
      have all:=moments_detect ho (d:=2) (by decide) (by omega) (fun i j=>by omega) (fun j:Fin q=>a j.succ) ker
      ext j;exact Fin.cases c0 all j
    · exact non ready
  rwa [←eqn,az,map_zero,zero_add]

/-- True coordinate space missing both ports; only the anchored branch
requires a zero at the first physical row. -/
def jointWithOrigin (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (e:ℕ):Submodule K (Vec K (s+1)):=
  (LinearMap.ker (diag b) ⊓ LinearMap.ker (diag (tau A b))) ⊓
    (if e=0 then LinearMap.ker (LinearMap.proj 0) else ⊤)

omit [CharZero K] in
theorem jointWithOrigin_iff {v:Vec K (s+1)} {e:ℕ}: v∈jointWithOrigin A b e ↔
    (b*v=0 ∧ tau A b*v=0) ∧ (e=0→v 0=0):=by
  by_cases z:e=0
  · simp [jointWithOrigin,z];intro _;rfl
  · simp [jointWithOrigin,z];rfl

omit [CharZero K] in
theorem jointWithOrigin_invariant (e:ℕ):(jointWithOrigin A b e).map (diag (nodes A))≤jointWithOrigin A b e:=by
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨⟨wb,wt⟩,zero⟩:=jointWithOrigin_iff.mp hv
  apply jointWithOrigin_iff.mpr;refine ⟨⟨?_,?_⟩,fun eqn=>?_⟩
  · change b*(nodes A*v)=0;rw [mul_left_comm,wb,mul_zero]
  · change tau A b*(nodes A*v)=0;rw [mul_left_comm,wt,mul_zero]
  · change nodes A 0*v 0=0;rw [zero eqn,mul_zero]

theorem twenty_joint_pure (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    {e:ℕ} (h:TwentyRanks A b e) :zeroSpace A 4≤jointWithOrigin A b e ∧
      jointWithOrigin A b e≤zeroSpace A 10 ⊓ LinearMap.ker (LinearMap.proj (Fin.last s)):=by
  classical
  let J:=jointWithOrigin A b e
  have D:=twenty_paid_reverse ha ho size h
  obtain ⟨hb,_,_,_,f9⟩:=twenty_final_row ha ho size h
  constructor
  · intro v hv
    apply jointWithOrigin_iff.mpr
    refine ⟨D.quartic_jointly_hidden ha ho (by decide) hv (f9 _ (zeroSpace_mono A (by decide) hv)),?_⟩
    intro eqn
    rcases h.flag with ⟨_,c2⟩|⟨bad,_⟩
    · exact zeroSpace_first_of_row (dirk_first_row ha c2) 4 hv
    · omega
  · intro v hj
    obtain ⟨⟨wb,wt⟩,orig⟩:=jointWithOrigin_iff.mp hj
    have mem:v∈treeSpace A 10:=by
      rw [(h.dual 10 7 (by decide) (by decide)).2.2.2,mem_annih]
      intro w wh
      obtain ⟨P,_,eqn⟩:=D.word_polynomial ha ho (D.nonlocal_cubic ha ho) (by decide:1≤7) (by decide) wh
      rw [row_apply];apply Finset.sum_eq_zero;intro i _
      have vi:tau A b i*v i=0:=congrFun wt i
      rw [eqn i]
      linear_combination P.eval (mirror A i)*vi
    have room:e≤1:=by rcases h.flag with ⟨eqn,_⟩|⟨eqn,_⟩ <;>omega
    refine ⟨pure_of_weight_zero ho (by omega:10-e≤10) ?_ h.full mem wb ?_,?_⟩
    · rcases h.flag with ⟨eqn,c2⟩|⟨eqn,_⟩
      · exact Or.inr ⟨by omega,dirk_first_row ha c2⟩
      · left;omega
    · intro _
      rcases h.flag with ⟨eqn,_⟩|⟨eqn,_⟩
      · exact Or.inl (orig eqn)
      · right;omega
    · change v (Fin.last s)=0
      exact (mul_eq_zero.mp (congrFun wb (Fin.last s))).resolve_left hb
end
end RKCert.Paired.Terminal

