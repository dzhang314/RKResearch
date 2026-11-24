module
public import RKCert.ERKOddReverseHorizon
public import RKCert.ERKThinReverseInvisibility
public import RKCert.OrderedBetaMoment
public import RKCert.DirkPolynomialMarked

@[expose] public section
/-! # The actual hidden carrier at an odd terminal-zero reverse horizon
The terminal compensation is retained as an actual stage coordinate.
The residue after subtracting it is identified without assuming node
separation or positive weights. -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.ERKEvenHidden RKCert.Paired.FiniteMidpoint RKCert.Paired.ReverseHull
open RKCert.Endpoint RKCert.OrderedGram Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b d:Vec K (s+1)}
noncomputable section

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem annih_terminal_sup (E:Submodule K (Vec K (s+1))) :
    annih (E⊔K∙terminal (K:=K) s)=annih E⊓LinearMap.ker (LinearMap.proj (Fin.last s)):=by
  ext z
  constructor
  · intro hz
    refine ⟨mem_annih.mpr (fun v hv=>mem_annih.mp hz _ ((show E≤E⊔K∙terminal (K:=K) s from le_sup_left) hv)),?_⟩
    change z (Fin.last s)=0
    rw [←row_terminal z]
    exact mem_annih.mp hz _ ((show K∙terminal (K:=K) s≤E⊔K∙terminal (K:=K) s from le_sup_right) (Submodule.mem_span_singleton_self _))
  · rintro ⟨hz,h0⟩
    apply mem_annih.mpr
    change E⊔K∙terminal (K:=K) s≤(row z).ker
    refine sup_le (mem_annih.mp hz) ((Submodule.span_singleton_le_iff_mem ..).mpr ?_)
    change row z (terminal s)=0
    rw [row_terminal]
    exact h0

/-- An original compensated hidden vector belongs to the actual defect
space, even with nonzero terminal correction. Full unmarked annihilator
coverage is neither assumed nor concluded. -/
theorem carrier_le_defects_odd (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b p)
    (paid:2*q+1≤p)(h1:1≤q)(ct:nodes A (Fin.last s)=1)(bt:b (Fin.last s)≠0)
    (dt:d (Fin.last s)=0)
    (support:∀w∈annih (treeSpace A q)⊓LinearMap.ker (LinearMap.proj (Fin.last s)),∀i,d i=0→w i=0) :
    carrier (nodes A) b d 0 (Fin.last s)≤zeroSpace A q:=by
  classical
  let t:=Fin.last s
  let e:=terminal (K:=K) s
  have c0:nodes A 0=0:=by
    change (∑i,A 0 i)=0
    exact Finset.sum_eq_zero (fun i _=>ha 0 i (Fin.zero_le i))
  have t0:t≠0:=by intro e;exact zero_ne_one (c0.symm.trans (e ▸ ct))
  intro v hv
  obtain ⟨off,mass⟩:=mem_ambientHidden.mp hv
  have o:v 0=0:=off _ (fun h=>((mem_blindRows 0).mp h).1 rfl) (Ne.symm t0)
  have mix:v∈treeSpace A q⊔K∙e:=by
    rw [←annih_annih_paired (treeSpace A q⊔K∙e),show annih (treeSpace A q⊔K∙e)=
      annih (treeSpace A q)⊓LinearMap.ker (LinearMap.proj t) from annih_terminal_sup _]
    apply mem_annih.mpr
    intro w hw
    rw [row_apply];apply Finset.sum_eq_zero
    intro i _
    by_cases dd:d i=0
    · rw [support w hw i dd,mul_zero]
    · rw [carrier_zero_on_active dt hv dd,zero_mul]
  obtain ⟨v0,hm,u,hu,rfl⟩:=Submodule.mem_sup.mp mix
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hu
  have v00:v0 0=0:=by simpa [e,terminal_at_ne (Ne.symm t0)] using o
  obtain ⟨c,pc⟩:=exists_poly_zeroSpace ho (by omega:q+1≤p) hm
  let P:K[X]:=ofFn (q+1) c
  have dP:P.natDegree≤q:=by have a:=ofFn_natDegree_lt (by omega:0<q+1) c;change P.natDegree<q+1 at a;omega
  have Tr:OrdinaryTrace A q v0 P:=⟨dP,by rw [evalNodes_ofFn];exact pc⟩
  have cz:P.coeff 0=0:=by
    have h:=origin_zeroSpace A ha _ Tr.pure
    change v0 0-P.eval (nodes A 0)=0 at h
    rw [v00,c0,zero_sub,neg_eq_zero,←coeff_zero_eq_eval_zero] at h
    exact h
  have pure:v0∈zeroSpace A q:=by
    suffices hz:P=0 by
      have Z:evalNodes A (0:K[X])=0:=by ext i;simp
      simpa only [hz,Z,sub_zero] using Tr.pure
    by_contra nz
    obtain ⟨R,rE⟩:=X_dvd_iff.mpr cz
    have rN:R≠0:=fun z=>nz (by rw [rE,z,mul_zero])
    have D:P.natDegree=1+R.natDegree:=by rw [rE,natDegree_mul X_ne_zero rN,natDegree_X]
    let S:K[X]:=(1-X)*R
    have dS:S.natDegree≤q:=natDegree_mul_le.trans (by rw [one_sub_X_natDegree];omega)
    have vzero:∀i,(1-nodes A i)*b i*v0 i=0:=by
      intro i
      have h:=carrier_mirror_weight_zero ct hv i
      by_cases e':i=t
      · subst i;rw [ct,sub_self,zero_mul,zero_mul]
      · simpa [e,terminal_at_ne e'] using h
    have ck:=Tr.pair_polynomial ho S (by omega)
    have nod:(row (weightedEval (nodes A) b S)) v0=0:=by
      rw [row_apply];apply Finset.sum_eq_zero
      intro i _
      rw [weightedEval_apply,show S.eval (nodes A i)=(1-nodes A i)*R.eval (nodes A i) by simp [S]]
      calc
        _=(((1-nodes A i)*b i)*v0 i)*R.eval (nodes A i):=by ring
        _=0:=by rw [vzero,zero_mul]
    have eq:P*S=(X-X^2)*R^2:=by rw [rE];dsimp only [S];ring
    rw [nod,eq,formalPrimitive_eq_treePrimitive,←betaIntegral_apply] at ck
    exact (beta_square_pos R rN).ne' ck.symm
  have bm:row b v0=0:=by
    have bz:=probe_zeroSpace ho (k:=0) (by omega) pure
    change probe A b 0 v0=0 at bz
    simpa only [probe,pow_zero,mul_one] using bz
  have bT:row b e=b t:=row_terminal b
  rw [map_add,map_smul,smul_eq_mul,bm,bT,zero_add] at mass
  have za:a=0:=(mul_eq_zero.mp mass).resolve_right bt
  simpa [za] using pure

/-- The whole genuine fourth forward grade vanishes on the actually paid
reverse ports; the companion inclusion builds the other side of the native
invariant-coordinate carrier, not a representation from arbitrary equations. -/
theorem balanced_odd_hidden_zero (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b (2*q+1))
    (h8:8≤q)(S:OddBalanced A b q)(Z:OddZeroReverse A b q) :
    let U:=carrier (nodes A) b (backSeed2 A b) 0 (Fin.last s)
    zeroSpace A 4≤U ∧ U≤zeroSpace A q ∧ U.map (diag (nodes A))≤U:=by
  let t:=Fin.last s
  let U:=carrier (nodes A) b (backSeed2 A b) 0 t
  change zeroSpace A 4≤U ∧ U≤zeroSpace A q ∧ U.map (diag (nodes A))≤U
  have y0:mirror A t=0:=S.lastReflect Z.firstZero
  have col:∀i,A i t=0:=fun i=>ha i _ (Fin.le_last i)
  have hsites:q-2+1<(Clock.headSites (mirror A) (backSeed2 A b)).card:=by have h:q≤(Clock.headSites (mirror A) (backSeed2 A b)).card:=Z.sites;omega
  refine ⟨?_,?_,carrier_invariant Z.lastNode⟩
  · intro v hv
    have ep:=ordered_thin_invisible ha ho hv (by decide) (by omega:4≤q-2) (by decide)
      (by omega:q+(q-2)+3≤2*q+1) (by omega) (by omega) t y0 col Z.lastSeed hsites
      (fun _ hw=>Z.poly_cover (by omega) hw)
    exact actual_defect_hidden ha ho (by omega) hv (fun i=>(ep i).1) (fun i=>(ep i).2)
  · apply carrier_le_defects_odd ha ho (by omega) (by omega) Z.lastNode S.lastLive Z.lastSeed
    intro w hw i dz
    obtain ⟨P,_,rep⟩:=Z.poly_cover (by omega) hw
    rw [←rep,weightedEval_apply,dz,mul_zero]
end
end RKCert.Paired.ERKOddHidden
