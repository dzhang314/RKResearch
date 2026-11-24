module
public import RKCert.ERKOddBroadLow
public import RKCert.ERKTwoVisibleFeeders

@[expose] public section
/-! # The full genuine hidden carrier in the broad linear-seed branch
The terminal vector in the feeder adapter is a *coordinate marker*, not
a substitute RK output row. All order and primitive facts use the original
b. This specialization of the generic feeder avoids a second proof. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Paired.ERKEvenHidden
open RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K}{b:Vec K (s+1)}
noncomputable section

def linearVisible (A:Fin (s+1)→Fin (s+1)→K)(b:Vec K (s+1))(i:Fin (s+1)):Prop:=
  backSeed1 A b i≠0∨b i≠0

def linearProbeMask (A:Fin (s+1)→Fin (s+1)→K)(b:Vec K (s+1)):Vec K (s+1):=by
  classical
  exact fun i=>if linearVisible A b i then 1 else 0

abbrev linearCarrier (A:Fin (s+1)→Fin (s+1)→K)(b:Vec K (s+1)):Submodule K (Vec K (s+1)):=
  carrier (nodes A) (terminal s) (linearProbeMask A b) 0 (Fin.last s)

theorem linear_probe_live (i:Fin (s+1)) : linearProbeMask A b i≠0↔linearVisible A b i:=by
  classical
  by_cases h:linearVisible A b i <;> simp [linearProbeMask,h]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem row_reversed_terminal (v:Vec K (s+1)) : row (terminal s) v=v (Fin.last s):=by
  calc
    row (terminal s) v=row v (terminal s):=by simp only [row_apply,mul_comm]
    _=v (Fin.last s):=row_terminal v

theorem linear_carrier_iff (bt:b (Fin.last s)≠0){v:Vec K (s+1)}:
    v∈linearCarrier A b↔v 0=0∧∀i,linearVisible A b i→v i=0:=by
  let t:=Fin.last s
  constructor
  · intro hv
    obtain ⟨mask,zero⟩:=mem_ambientHidden.mp hv
    have last:v t=0:=(row_reversed_terminal v).symm.trans zero
    have first:v 0=0:=by
      by_cases e:(0:Fin (s+1))=t
      · rwa [e]
      · exact mask 0 (fun g=>((mem_blindRows 0).mp g).1 rfl) e
    refine ⟨first,?_⟩
    intro i hi
    by_cases e:i=t
    · rwa [e]
    exact mask i (fun g=>(linear_probe_live i).mpr hi ((mem_blindRows i).mp g).2.2.1) e
  · rintro ⟨v0,vis⟩
    have vt:v t=0:=vis t (Or.inr bt)
    apply mem_ambientHidden.mpr
    refine ⟨?_,(row_reversed_terminal v).trans vt⟩
    intro i ng nt
    by_cases n0:i=0
    · rwa [n0]
    by_cases vi:linearVisible A b i
    · exact vis i vi
    exact False.elim (ng ((mem_blindRows i).mpr ⟨n0,nt,not_ne_iff.mp (fun nz=>vi ((linear_probe_live i).mp nz)),
      by rw [terminal_at_ne nt,mul_zero]⟩))

theorem linear_carrier_clock (bt:b (Fin.last s)≠0):
    (linearCarrier A b).map (diag (nodes A))≤linearCarrier A b:=by
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨v0,vis⟩:=(linear_carrier_iff bt).mp hv
  exact (linear_carrier_iff bt).mpr ⟨by rw [diag_apply,v0,mul_zero],fun i h=>by rw [diag_apply,vis i h,mul_zero]⟩

theorem BroadLinearCover.pure_off_linear (B:BroadLinearCover A b 8 7)
    (ho:HasTreeOrderAtLeast A b 17){v:Vec K (s+1)}
    (vis:∀i,linearVisible A b i→v i=0):v∈zeroSpace A 8:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  have e:v∈treeSpace A 8:=by
    rw [←annih_annih_paired (treeSpace A 8)]
    apply mem_annih.mpr
    intro x hx
    rw [row_apply];apply Finset.sum_eq_zero
    intro i _
    by_cases z:backSeed1 A b i=0
    · rw [B.support hx z,mul_zero]
    · rw [vis i (Or.inl z),zero_mul]
  obtain ⟨a,rep⟩:=exists_poly_zeroSpace ho (by decide:8+1≤17) e
  let P:K[X]:=ofFn 9 a
  have pd:P.natDegree≤8:=by have e:=ofFn_natDegree_lt (by decide:0<9) a;change P.natDegree<9 at e;omega
  have tr:OrdinaryTrace A 8 v P:=⟨pd,by rw [evalNodes_ofFn];exact rep⟩
  have P0:P=0:=by
    by_contra nz
    have ss:row (weightedEval (nodes A) b P) v=0:=by
      rw [row_apply];apply Finset.sum_eq_zero
      intro i _
      by_cases e:b i=0
      · rw [weightedEval_apply,e,mul_zero,zero_mul]
      · rw [vis i (Or.inr e),mul_zero]
    have h:=tr.pair_polynomial ho P (by omega)
    rw [ss,formalPrimitive_eq_treePrimitive,←pow_two] at h
    have pp:=RKCert.OrderedGram.pow_square_pos 0 P nz
    rw [pow_zero,one_mul] at pp
    exact pp.ne' h.symm
  have E:evalNodes A (0:K[X])=0:=by ext i;simp
  simpa only [P0,E,sub_zero] using tr.pure

theorem BroadLinearCover.origin_visible (B:BroadLinearCover A b 8 7)
    (ho:HasTreeOrderAtLeast A b 17)(ha:StrictLower A):linearVisible A b 0:=by
  classical
  by_contra absent
  let e:Vec K (s+1):=Pi.single 0 1
  have hh:=B.pure_off_linear ho (v:=e) (by
    intro i vi
    have nz:i≠0:=fun z=>absent (z ▸ vi)
    simp [e,Pi.single_eq_of_ne nz])
  have z:=origin_zeroSpace A ha 8 hh
  change e 0=0 at z
  have h:(1:K)=0:=by simpa only [e,Pi.single_eq_same] using z
  exact one_ne_zero h

theorem BroadLinearCover.low_vis (B:BroadLinearCover A b 8 7)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17):
    ∀v∈zeroSpace A 4,∀i,linearVisible A b i→v i=0:=by
  intro v vf i vi
  obtain ⟨Q,P,qd,pd,fit⟩:=broad_linear_two_traces ho B vf (by decide) (by decide) (by decide)
  have ev:=ordered_broad_invisible_given_reps ha ho B Q P qd (by omega) (by omega) (by omega) (by omega) fit i
  rcases vi with n|n
  · exact (mul_eq_zero.mp ev.1).resolve_left n
  · exact (mul_eq_zero.mp ev.2).resolve_left n

theorem BroadLinearCover.feeder (B:BroadLinearCover A b 8 7)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(bt:b (Fin.last s)≠0):
    finrank K (zeroSpace A 3)+2≤finrank K (linearCarrier A b):=by
  let d:=linearProbeMask A b
  let e:=terminal (K:=K) s
  have bt':e (Fin.last s)≠0:=by rw [show e (Fin.last s)=1 from terminal_at_last];exact one_ne_zero
  have ev(i:Fin (s+1)):evenVisible A e d i↔linearVisible A b i:=by
    constructor
    · rintro (z|z)
      · exact (linear_probe_live i).mp z
      by_cases t:i=Fin.last s
      · exact Or.inr (t.symm ▸ bt)
      have ee:e i=0:=terminal_at_ne t
      rw [ee,mul_zero] at z
      exact False.elim (z rfl)
    · intro h;exact Or.inl ((linear_probe_live i).mpr h)
  have Fs:zeroSpace A 3≤linearCarrier A b:=by
    intro v vf
    apply (linear_carrier_iff bt).mpr
    exact ⟨origin_zeroSpace A ha 3 vf,B.low_vis ha ho v (zeroSpace_mono A (by decide:3≤4) vf)⟩
  obtain ⟨i,j,hi,hj,i0,j0,jg⟩:=two_different_visible_nonzero (d:=backSeed1 A b) ho (by decide)
  have ss(i:Fin (s+1))(h:evenVisible A b (backSeed1 A b) i):linearVisible A b i:=by
    rcases h with e|e
    · exact Or.inl e
    · exact Or.inr (mul_ne_zero_iff.mp e).2
  have counts:=hidden_feeder_two_rank (b:=e) (d:=d) ha
    (fun v hv i h=>B.low_vis ha ho v hv i ((ev i).mp h)) Fs bt'
    ⟨i,j,(ev i).mpr (ss i hi),(ev j).mpr (ss j hj),i0,j0,jg⟩
  rw [←carrier_rank bt'] at counts
  exact counts
end
end RKCert.Paired.ReverseHull

