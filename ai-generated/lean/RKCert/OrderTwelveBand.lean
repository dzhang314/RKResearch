module
public import RKCert.OrderTwelveMomentPackets
public import RKCert.OrderTwelveSaturation
@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Endpoint Polynomial Module
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)} {i:Fin (s+1)}

noncomputable def pBand (A : Fin (s+1) → Fin (s+1) → K) : Submodule K (Vec K (s+1)) :=
  LinearMap.range (polyEval A 6)
def endZero (A : Fin (s+1) → Fin (s+1) → K) (j : ℕ) (i : Fin (s+1)) :
    Submodule K (Vec K (s+1)) := zeroSpace A j ⊓ (LinearMap.proj i).ker
def escape7 (A : Fin (s+1) → Fin (s+1) → K) : Submodule K (Vec K (s+1)) :=
  zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))

omit [CharZero K] in
theorem pBand_le (A : Fin (s+1)→Fin (s+1)→K) {j:ℕ} (hj:6≤j) :
    pBand A ≤ treeSpace A j := by
  rintro x ⟨a,rfl⟩
  exact treeSpace_mono A hj (polyEval_mem_treeSpace A 6 a)
omit [CharZero K] in
theorem polyEval_at (A : Fin (s+1)→Fin (s+1)→K) (q:ℕ) (a:Fin (q+1)→K) (i:Fin (s+1)) :
    polyEval A q a i = ∑ j, a j*(nodes A i)^j.val := by
  rw [polyEval_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,normTree_bush]
omit [CharZero K] in
theorem probe_polyEval_moment (ho : HasTreeOrderAtLeast A b 12) {k:ℕ}
    (hk:k+7≤12) (a:Fin 7→K) :
    probe A b k (polyEval A 6 a)=moment a 1 k := by
  rw [probe_polyEval ho (by omega)]
  simp only [moment,one_pow,mul_one,Nat.add_comm]
omit [CharZero K] in
theorem first_zero {a:Fin 7→K} {j:ℕ} (ha:StrictLower A) (hz:polyEval A 6 a∈zeroSpace A j) :
    a 0=0 := by
  have h := origin_zeroSpace A ha j hz
  change polyEval A 6 a 0=0 at h
  rwa [polyEval_first ha] at h

theorem last_zero_separation (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hi:nodes A i=1) (a:Fin 7→K) (hx:polyEval A 6 a∈endZero A 7 i) : a=0 := by
  have hh := Submodule.mem_inf.mp hx
  apply last_zero_decoder a (first_zero ha hh.1)
  · have hp : polyEval A 6 a i=0 := hh.2
    simpa only [polyEval_at,hi,one_pow,mul_one] using hp
  · intro k
    rw [← probe_polyEval_moment ho (by have := k.isLt;omega)]
    exact probe_zeroSpace ho (by have := k.isLt;omega) hh.1

omit [CharZero K] in
theorem band_rank_add {U : Submodule K (Vec K (s+1))}
    (h : ∀ a:Fin 7→K, polyEval A 6 a∈U → a=0) :
    finrank K ↥(pBand A ⊔ U) = 7+finrank K U := by
  have hj : Function.Injective (polyEval A 6) :=
    (injective_iff_map_eq_zero _).mpr fun a hz => h a (hz ▸ U.zero_mem)
  have hr : finrank K (pBand A)=7 := by
    unfold pBand
    rw [LinearMap.finrank_range_of_inj hj,Module.finrank_fin_fun]
  have hmeet : pBand A ⊓ U=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨a,ha⟩ := (Submodule.mem_inf.mp hv).1
    have hz := h a (ha ▸ (Submodule.mem_inf.mp hv).2)
    rw [hz,map_zero] at ha
    exact (Submodule.mem_bot K).mpr ha.symm
  have he:=Submodule.finrank_sup_add_finrank_inf_eq (pBand A) U
  have hb : finrank K ↥(pBand A ⊓ U)=0 := Submodule.finrank_eq_zero.mpr hmeet
  omega
theorem f7_end_rank (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:nodes A i=1) : finrank K (endZero A 7 i)≤7 := by
  have hc:=hs.caps 7 (by decide)
  have hh:=band_rank_add (last_zero_separation ha ho hi)
  have he := Submodule.finrank_mono (show pBand A ⊔ endZero A 7 i ≤ treeSpace A 7 from
    sup_le (pBand_le A (by decide)) (inf_le_left.trans (zeroSpace_le_treeSpace A 7)))
  omega
omit [CharZero K] in
theorem end_rank_loss (A : Fin (s+1)→Fin (s+1)→K) (j:ℕ) (i:Fin (s+1)) :
    finrank K (zeroSpace A j)≤finrank K (endZero A j i)+1 := by
  let Z := zeroSpace A j
  let T := endZero A j i
  have ht : T≤Z := inf_le_left
  let f : Z→ₗ[K]K := (LinearMap.proj i).comp Z.subtype
  have hker : f.ker=T.comap Z.subtype := by
    ext x
    change (x.val i=0) ↔ x.val∈endZero A j i
    exact ⟨fun h=>⟨x.property,h⟩,fun h=> h.2⟩
  have hr:=LinearMap.finrank_range_add_finrank_ker f
  rw [hker,(Submodule.comapSubtypeEquivOfLe ht).finrank_eq] at hr
  have hh:=Submodule.finrank_le f.range
  rw [Module.finrank_self] at hh
  change finrank K f.range+finrank K (endZero A j i)=finrank K (zeroSpace A j) at hr
  omega
theorem f6_noninvariant (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:nodes A i=1) :
    ¬(zeroSpace A 6).map (diag (nodes A))≤zeroSpace A 6 := by
  intro h
  have h7 := f7_end_rank ha ho hs hi
  have h8 := end_rank_loss A 7 i
  have hg := forward_invariant_hermite_rank ha ho (j:=6) (by decide) (zeroSpace A 6) le_rfl
    (fun _ hv=> h (Submodule.mem_map_of_mem hv))
  change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 7) at hg
  have h6 := hs.f6
  omega
theorem escape7_le_end (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) : escape7 A≤endZero A 7 i := by
  have hw (v) (hv:v∈zeroSpace A 6) := f6_vanish_at_last_active ha ho hs hi hl hv
  apply sup_le
  · intro v hv
    exact ⟨zeroSpace_mono A (by decide : 6≤7) hv, hw v hv⟩
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨diag_zeroSpace A 6 hv,by simp [hw v hv]⟩
theorem escape7_rank (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) : finrank K (escape7 A)=7 := by
  have h1 := Submodule.finrank_mono (escape7_le_end ha ho hs hi hl)
  have h2 := f7_end_rank ha ho hs (active_last_normal ha hs hi hl)
  have h3 : zeroSpace A 6<escape7 A := lt_of_le_of_ne le_sup_left
    (fun e => f6_noninvariant ha ho hs (active_last_normal ha hs hi hl)
      ((show (zeroSpace A 6).map (diag (nodes A))≤escape7 A from le_sup_right).trans (le_of_eq e.symm)))
  have h4 := Submodule.finrank_lt_finrank_of_lt h3
  have h5 := hs.f6
  omega
theorem escape7_exact (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) : escape7 A=endZero A 7 i := by
  exact Submodule.eq_of_le_of_finrank_le (escape7_le_end ha ho hs hi hl)
    ((f7_end_rank ha ho hs (active_last_normal ha hs hi hl)).trans_eq
      (escape7_rank ha ho hs hi hl).symm)
theorem e7_exact (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) :
    treeSpace A 7=pBand A ⊔ escape7 A := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · rw [escape7_exact ha ho hs hi hl]
    exact sup_le (pBand_le _ (by decide)) (inf_le_left.trans (zeroSpace_le_treeSpace A 7))
  · have hf := hs.caps 7 (by decide)
    have hh := band_rank_add (A:=A) (U:=escape7 A) (fun a hav =>
      last_zero_separation ha ho (active_last_normal ha hs hi hl) a (escape7_le_end ha ho hs hi hl hav))
    rw [escape7_rank ha ho hs hi hl] at hh
    omega

omit [CharZero K] in
theorem coefficient_packet {P : K[X]} (hp:P.natDegree≤6) :
    P = (by classical exact Polynomial.ofFn 7 (fun j => P.coeff j.val)) := by
  classical
  exact (Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : P.natDegree<7)).symm
omit [CharZero K] in
theorem polynomial_packet_val_one {P : K[X]} (hp:P.natDegree≤6) :
    P.eval 1=∑ j : Fin 7, P.coeff j.val := by
  classical
  conv_lhs => rw [coefficient_packet hp,Polynomial.ofFn_eq_sum_monomial]
  simp [Polynomial.eval_finsetSum]

theorem mesh_at_end (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) :
    (Pi.single i (1:K) : Vec K (s+1))-evalNodes A mesh6∈zeroSpace A 6 := by
  classical
  have hci:=active_last_normal ha hs hi hl
  obtain ⟨P,hp,hz⟩:=exists_poly_zeroSpace_charZero A (tail_col_mem ha hs hi hl (j:=i) le_rfl)
  let a : Fin 7→K := fun j=>P.coeff j.val
  have evp := evalNodes_eq_polyEval A P hp
  have hzi := f6_vanish_at_last_active ha ho hs hi hl hz
  have heval1 : P.eval 1=1 := by
    change (Pi.single i (1:K) : Vec K (s+1)) i-P.eval (nodes A i)=0 at hzi
    rwa [Pi.single_eq_same,hci,sub_eq_zero,eq_comm] at hzi
  have hn0 : nodes A 0=0 := by
    unfold nodes
    exact Finset.sum_eq_zero (fun j _ => ha 0 j (by simp))
  have hci0 : i≠0 := by
    intro e
    rw [e,hn0] at hci
    exact zero_ne_one hci
  have hz0 := origin_zeroSpace A ha 6 hz
  have h0 : a 0=0 := by
    change (Pi.single i (1:K) : Vec K (s+1)) 0-P.eval (nodes A 0)=0 at hz0
    rw [Pi.single_eq_of_ne hci0.symm,hn0,← Polynomial.coeff_zero_eq_eval_zero,zero_sub,neg_eq_zero] at hz0
    exact hz0
  have hm (k:ℕ) (hk:k≤5) : moment a 1 k = b i := by
    have hv := probe_zeroSpace ho (n:=6) (k:=k) (by omega) hz
    change probe A b k (Pi.single i (1:K)-evalNodes A P)=0 at hv
    rw [map_sub,sub_eq_zero,evp] at hv
    rw [← probe_polyEval_moment ho (by omega)]
    rw [← hv]
    simp [probe,row_apply,Pi.single_apply,Finset.sum_ite_eq',hci,mul_ite]
  have hcoeff := terminal_decoder a h0 (by rw [← polynomial_packet_val_one hp,heval1])
    (fun k => by rw [hm _ (by have := k.isLt;omega),hm _ (by have := k.isLt;omega),sub_self])
  have hP : P=mesh6 := by
    rw [coefficient_packet hp]
    change Polynomial.ofFn 7 a = mesh6
    rw [hcoeff]
    rfl
  rwa [hP] at hz

end RKCert.Paired.OrderTwelve

