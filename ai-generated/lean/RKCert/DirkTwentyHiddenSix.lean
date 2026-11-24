module
public import RKCert.DirkTwentyOmitted
public import RKCert.DirkFifthGridPorts
public import RKCert.SexticFixed20
public import RKCert.DirkTenInvariantEscape
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.Endpoint
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section
set_option maxHeartbeats 1500000

omit [CharZero K] in
theorem contrast_zero_hidden {f:Vec K (s+1)} {Q:K[X]}
    (zero:Q=0) (fit:∀i,tau A b i≠0→f i=Q.eval (mirror A i))
    (off:∀i,tau A b i=0→b i*f i=0) (fo:f 0=0):f∈jointWithOrigin A b 0:=by
  have on(i:Fin (s+1)) (nz:tau A b i≠0):f i=0:=by simpa [zero] using fit i nz
  apply jointWithOrigin_iff.mpr
  refine ⟨⟨?_,?_⟩,fun _=>fo⟩ <;> ext i
  · by_cases h:tau A b i=0
    · exact off i h
    · simp [on i h]
  · by_cases h:tau A b i=0
    · simp [h]
    · simp [on i h]

/-- The missing fifth-degree numerator is forced to zero by two actual,
different, diagonally refunded clean ports and one omitted fixed root. -/
theorem twenty_five_hidden (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (sp:((X-1)*lobatto (K:=K) 10).Splits) :zeroSpace A 5≤jointWithOrigin A b 0:=by
  obtain ⟨h,org,ten⟩:=twenty_origin ha ho size
  let D:=twenty_paid_reverse ha ho size h
  have cap:=twenty_clean_budget ha ho size
  obtain ⟨v,_,rr,miss⟩:=omitted_ten_grid (cleanSites A b) (n:=1) (by omega) sp
  let z:=v 0
  intro f hf
  obtain ⟨Q,dq,fit,off,θ,tr,active⟩:=D.port_contrast ha ho (by decide) (by decide) hf
    (ten _ (zeroSpace_mono A (by decide) hf))
  have qz:Q.eval z=0:=twenty_omitted_root ha ho size tr (by decide) (by omega) active (rr 0) (miss 0)
  apply contrast_zero_hidden _ fit off (zeroSpace_first_of_row org 5 hf)
  by_contra nz
  obtain ⟨i,l,bi,ti,bl,tl,un,vn,vu,first,second⟩:=D.two_paid_ports ha ho (by decide) (by decide) tr nz active
  have clean₁:=mem_cleanSites i bi ti
  have clean₂:=mem_cleanSites l bl tl
  exact nz (RKCert.PaidFifth.lobatto10_omitted_quintic (twenty_clean_grid ha ho size i bi ti)
    (twenty_clean_grid ha ho size l bl tl) (rr 0) un vn vu (fun eqn=>miss 0 (eqn ▸ clean₁))
    (fun eqn=>miss 0 (eqn ▸ clean₂)) Q dq qz (fun k=>first k.val (by have:=k.isLt;omega))
    (fun k=>second k.val (by have:=k.isLt;omega)))

/-- F5 together with its true clock image already occupies at least four
invisible physical coordinates: a three-dimensional invariant F5 would
pay four dimensions by the original incoming Hermite inequality. -/
theorem twenty_invisible_four (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (five:zeroSpace A 5≤jointWithOrigin A b 0):4≤finrank K (jointWithOrigin A b 0):=by
  obtain ⟨h,_,_⟩:=twenty_origin ha ho size
  by_contra! small
  have rank:=h.five.1
  have eqn:=Submodule.eq_of_le_of_finrank_le five (by omega)
  have inv: (zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5:=eqn ▸ jointWithOrigin_invariant 0
  have grow:=dirk_forward_invariant_incoming ha ho (j:=5) (by decide) (fun x hx=>inv ⟨x,hx,rfl⟩)
  change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at grow
  have gr:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by decide)
  have low:=h.three
  have le:=Submodule.finrank_mono five
  omega

/-- With at least four jointly invisible original coordinates, at least
five fixed knots are absent from clean support. Two actual degree-six
primitive observations at a sixth knot now force the sixth grade hidden. -/
theorem twenty_six_hidden (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (sp:((X-1)*lobatto (K:=K) 10).Splits) :zeroSpace A 6≤jointWithOrigin A b 0:=by
  obtain ⟨h,org,ten⟩:=twenty_origin ha ho size
  let D:=twenty_paid_reverse ha ho size h
  have four:=twenty_invisible_four ha ho size (twenty_five_hidden ha ho size sp)
  have cap:=twenty_clean_budget ha ho size
  obtain ⟨a,inj,roots,miss⟩:=omitted_ten_grid (cleanSites A b) (n:=5) (by omega) sp
  intro f hf
  obtain ⟨Q,dq,fit,off,θ,tr,active⟩:=D.port_contrast ha ho (by decide) (by decide) hf
    (ten _ (zeroSpace_mono A (by decide) hf))
  have qa(i:Fin 5):Q.eval (a i)=0:=twenty_omitted_root ha ho size tr (by decide) (by omega) active (roots i) (miss i)
  apply contrast_zero_hidden _ fit off (zeroSpace_first_of_row org 6 hf)
  by_contra nz
  let y:=mirror A
  have ac(i:Fin (s+1))(v:diag y θ i≠0):b i≠0 ∧ tau A b i=0:=
    active i (fun zero=>v (by rw [diag_apply,zero,mul_zero]))
  obtain ⟨i,vi,bi,ti,_,tests⟩:=D.physical_reverse_pivot ha ho (D.nonlocal_cubic ha ho) (by decide) (by decide)
    (tr.clock (by decide)) ac (mul_ne_zero X_ne_zero nz)
  have yn:y i≠0:=fun zero=>vi (by change y i*θ i=0;rw [zero,zero_mul])
  have clean:=mem_cleanSites i bi ti
  have fresh(k:Fin 5):y i≠a k:=fun eqn=>miss k (eqn ▸ clean)
  have j₁: (Paired.primitive (X*Q)).eval (y i)=0:=by simpa only [pow_zero,one_mul,formalPrimitive_eq_treePrimitive] using tests 0 (by decide)
  have j₂: (Paired.primitive (X^2*Q)).eval (y i)=0:=by simpa only [pow_one,pow_two,mul_assoc,formalPrimitive_eq_treePrimitive] using tests 1 (by decide)
  exact nz (RKCert.Sextic.lobatto10_five_omitted a (y i) Q inj roots (twenty_clean_grid ha ho size i bi ti) fresh yn dq qa j₁ j₂)

theorem twenty_eight_impossible (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (sp:((X-1)*lobatto (K:=K) 10).Splits):False:=by
  obtain ⟨h,_,_⟩:=twenty_origin ha ho size
  have inc:jointWithOrigin A b 0≤zeroSpace A 10:=(twenty_joint_pure ha ho size h).2.trans inf_le_left
  exact grade_six_escapes_ten ha ho (by decide) (by simpa using h.ten.le) (by simpa using h.eleven)
    inc (jointWithOrigin_invariant _) (twenty_six_hidden ha ho size sp)

end
end RKCert.Paired.Terminal
