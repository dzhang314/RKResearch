module
public import RKCert.OrderTwelveMeshPolynomials
public import RKCert.OrderTwelveStaircase
@[expose] public section
/-! # Finite polynomial leakage of the two late order-twelve bands -/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)} {i:Fin (s+1)}

theorem mesh7_in_escape (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0) :
    evalNodes A degreeSevenMesh∈escape7 A := by
  classical
  let d : Vec K (s+1) := Pi.single i (1:K)-evalNodes A mesh6
  have hc := active_last_normal ha hs hi hl
  have hd : d∈zeroSpace A 6 := mesh_at_end ha ho hs hi hl
  have hF : zeroSpace A 6≤escape7 A := le_sup_left
  have hD : (zeroSpace A 6).map (diag (nodes A))≤escape7 A := le_sup_right
  have hh : diag (nodes A) d-d ∈ escape7 A :=
    (escape7 A).sub_mem (hD (Submodule.mem_map_of_mem hd)) (hF hd)
  have ee : diag (nodes A) d-d= -evalNodes A degreeSevenMesh := by
    ext j
    by_cases h : j=i
    · subst j
      simp [d,evalNodes,degreeSevenMesh,hc]
    · simp only [d,evalNodes,degreeSevenMesh,diag_apply,Pi.sub_apply,Pi.neg_apply,
        Pi.single_eq_of_ne h,eval_mul,eval_sub,eval_X,eval_one]
      ring
  rw [ee] at hh
  exact (escape7 A).neg_mem_iff.mp hh

theorem ghost7_leak (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    {v:Vec K (s+1)} (hv:v∈zeroSpace A 7) :
    ∃ a:K, v-a • evalNodes A ghost7∈escape7 A := by
  have he := zeroSpace_le_treeSpace A 7 hv
  rw [e7_exact ha ho hs hi hl] at he
  obtain ⟨y,⟨c,rfl⟩,z,hz,rfl⟩:=Submodule.mem_sup.mp he
  have hc : polyEval A 6 c∈zeroSpace A 7 := by
    have hh := (zeroSpace A 7).sub_mem hv ((escape7_le_end ha ho hs hi hl hz).1)
    simpa only [add_sub_cancel_right] using hh
  have h := ghost7_decoder c (first_zero ha hc) (fun k => by
    rw [← probe_polyEval_moment ho (by have := k.isLt;omega)]
    exact probe_zeroSpace ho (by have := k.isLt;omega) hc)
  refine ⟨c 6/462,?_⟩
  have hp : polyEval A 6 c=(c 6/462) • evalNodes A ghost7 := by
    rw [evalNodes_eq_polyEval A ghost7 ghost7_natDegree,←map_smul]
    congr 1
    simpa only [ghost7_coeff] using h
  simpa only [hp,add_sub_cancel_left] using hz

theorem ghost8_leak (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hi:nodes A i=1) {Z:Submodule K (Vec K (s+1))}
    (he:treeSpace A 8=pBand A ⊔ Z) (ht:Z≤endZero A 8 i)
    {v:Vec K (s+1)} (hv:v∈endZero A 8 i) :
    ∃ a:K, v-a • evalNodes A ghost8∈Z := by
  have hea := zeroSpace_le_treeSpace A 8 hv.1
  rw [he] at hea
  obtain ⟨y,⟨c,rfl⟩,z,hz,rfl⟩:=Submodule.mem_sup.mp hea
  have hc : polyEval A 6 c∈endZero A 8 i := by
    have hh := (endZero A 8 i).sub_mem hv (ht hz)
    simpa only [add_sub_cancel_right] using hh
  have h1 : (∑j,c j)=0 := by
    have hh : polyEval A 6 c i=0 := hc.2
    simpa only [polyEval_at,hi,one_pow,mul_one] using hh
  have h := ghost8_decoder c (first_zero ha hc.1) h1 (fun k=>by
    rw [←probe_polyEval_moment ho (by have := k.isLt;omega)]
    exact probe_zeroSpace ho (by have := k.isLt;omega) hc.1)
  refine ⟨c 6/(-210),?_⟩
  have hp : polyEval A 6 c=(c 6/(-210)) • evalNodes A ghost8 := by
    rw [evalNodes_eq_polyEval A ghost8 ghost8_natDegree,←map_smul]
    congr 1
    simpa only [ghost8_coeff] using h
  rw [hp,add_sub_cancel_left]
  exact hz

omit [CharZero K] in
theorem chain_rank_cap {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (n:ℕ) : finrank K (chain (diag (nodes A)) U w n)≤finrank K U+n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    let z := (diag (nodes A)^n) w
    have hz : finrank K (Submodule.span K {z})≤1 :=
      (finrank_span_le_card ({z}:Set (Vec K (s+1)))).trans (by simp)
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (chain (diag (nodes A)) U w n) (Submodule.span K {z})
    change finrank K (chain (diag (nodes A)) U w (n+1))+
      finrank K ↥(chain (diag (nodes A)) U w n ⊓ Submodule.span K {z}) =
      finrank K (chain (diag (nodes A)) U w n)+finrank K (Submodule.span K {z}) at hs
    omega

omit [CharZero K] in
theorem band_polynomial_zero (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    {Z:Submodule K (Vec K (s+1))} {j:ℕ}
    (hZ:finrank K Z≤j) (hE:finrank K ↥(pBand A ⊔ Z)=7+j) {P:K[X]}
    (hp:P.natDegree≤6) (hP:evalNodes A P∈Z) : P=0 := by
  classical
  have hi : Function.Injective (polyEval A 6) := (injective_iff_map_eq_zero _).mpr
    (fun a h=>explicit_poly_separated ha ho (by decide) (by omega) a
      (h ▸ (zeroSpace A 6).zero_mem))
  have hp7 : finrank K (pBand A)=7 := by unfold pBand;rw [LinearMap.finrank_range_of_inj hi,Module.finrank_fin_fun]
  have dim := Submodule.finrank_sup_add_finrank_inf_eq (pBand A) Z
  have hbot : pBand A ⊓ Z=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hmem : evalNodes A P∈pBand A ⊓ Z := ⟨⟨_,(evalNodes_eq_polyEval A P hp).symm⟩,hP⟩
  have hzero : evalNodes A P=0 := (Submodule.mem_bot K).mp (hbot ▸ hmem)
  exact explicit_separated ha ho (by decide) (by omega) P hp (hzero ▸ (zeroSpace A 6).zero_mem)

omit [CharZero K] in
theorem endZero_next (j:ℕ) :
    endZero A j i ⊔ (endZero A j i).map (diag (nodes A))≤endZero A (j+1) i := by
  apply sup_le
  · intro v hv
    exact ⟨zeroSpace_mono A (by omega) hv.1,hv.2⟩
  · rintro _ ⟨v,hv,rfl⟩
    have h : v i=0 := hv.2
    exact ⟨diag_zeroSpace A j hv.1,by change nodes A i*v i=0;rw [h,mul_zero]⟩

omit [CharZero K] in
theorem chain_le_next {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {n:ℕ} :
    chain (diag (nodes A)) U w n≤chain (diag (nodes A)) U w (n+1) := by
  exact le_sup_left

theorem no_double_leak_both (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hh:HeadData A r U w)
    (h8:treeSpace A 8=pBand A ⊔ chain (diag (nodes A)) U w (r+3))
    (h9:treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U w (r+4))
    (h9r:finrank K (treeSpace A 9)=16)
    {v:Vec K (s+1)} (hv:v∈endZero A 8 i) (hcv:diag (nodes A) v∈endZero A 8 i) :
    v∈chain (diag (nodes A)) U w (r+3) ∧
      diag (nodes A) v∈chain (diag (nodes A)) U w (r+3) := by
  let Ck := diag (nodes A)
  let Z7 := chain Ck U w (r+2)
  let Z8 := chain Ck U w (r+3)
  let Z9 := chain Ck U w (r+4)
  have h78 : Z7⊔Z7.map Ck=Z8 := chain_sup_map hh.inv (by omega)
  have h89 : Z8⊔Z8.map Ck=Z9 := chain_sup_map hh.inv (by omega)
  have hz7 : escape7 A=Z7 := hh.f7tail
  have h7t : Z7≤endZero A 7 i := hz7 ▸ escape7_le_end ha ho hs hi hl
  have h8t: Z8≤endZero A 8 i := by rw [←h78];exact (sup_le_sup h7t (Submodule.map_mono h7t)).trans (endZero_next 7)
  obtain ⟨a,ea⟩ := ghost8_leak ha ho (active_last_normal ha hs hi hl) h8 h8t hv
  obtain ⟨b',eb⟩:= ghost8_leak ha ho (active_last_normal ha hs hi hl) h8 h8t hcv
  let P : K[X] := X*(a • ghost8)-b' • ghost8+(35/22*a) • degreeSevenMesh
  have hP : evalNodes A P∈Z9 := by
    have g : evalNodes A degreeSevenMesh ∈ Z9 := by
      have g7 : evalNodes A degreeSevenMesh ∈ Z7 := by
        rw [←hz7];exact mesh7_in_escape ha ho hs hi hl
      exact chain_le_next (chain_le_next g7)
    have ea' : Ck (v-a • evalNodes A ghost8)∈Z9 := by
      rw [←h89]
      exact (show Z8.map Ck≤Z8⊔Z8.map Ck from le_sup_right) (Submodule.mem_map_of_mem ea)
    have eb' : Ck v-b' • evalNodes A ghost8∈Z9 := chain_le_next eb
    have q := Z9.add_mem (Z9.sub_mem eb' ea') (Z9.smul_mem (35/22*a) g)
    have e : (Ck v-b' • evalNodes A ghost8)-Ck (v-a • evalNodes A ghost8)+
      (35/22*a) • evalNodes A degreeSevenMesh=evalNodes A P := by
      ext j
      simp [Ck,P,evalNodes,Polynomial.eval_smul]
    rwa [e] at q
  have hd : P.natDegree≤6 := by
    have h7 : P.natDegree≤7 := by
      unfold P
      apply (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_smul_le ..).trans mesh7_degree_le))
      apply (natDegree_sub_le _ _).trans (max_le ?_ ((natDegree_smul_le ..).trans (ghost8_natDegree.trans (by decide))))
      exact natDegree_mul_le.trans (Nat.add_le_add (by simp) ((natDegree_smul_le ..).trans ghost8_natDegree))
    have g6 := ghost8_coeff (K:=K) (6:Fin 7)
    change (ghost8:K[X]).coeff 6= -210 at g6
    have g7 : (ghost8:K[X]).coeff 7=0 := coeff_eq_zero_of_natDegree_lt (by have := ghost8_natDegree (K:=K);omega)
    have c7 : P.coeff 7=0 := by
      simp only [P,coeff_add,coeff_sub,AddMonoidAlgebra.coeff_smul_apply,coeff_X_mul,g6,g7,mesh7_coeff7,smul_eq_mul]
      ring
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rcases Nat.eq_or_lt_of_le (show 7≤n by omega) with e|e
    · rwa [←e]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hc : finrank K Z9≤9 := by
    have h := chain_rank_cap (A:=A) (U:=U) (w:=w) (r+4)
    have hr:=hh.rank
    change finrank K Z9≤finrank K U+(r+4) at h
    omega
  have he : finrank K ↥(pBand A ⊔ Z9)=7+9 := by rw [←h9];exact h9r
  have hp := band_polynomial_zero ha ho hc he hd hP
  obtain ⟨az,bz⟩:=ghost8_shift_scalar a b' hp
  exact ⟨by simpa only [az,zero_smul,sub_zero] using ea,
    by simpa only [bz,zero_smul,sub_zero] using eb⟩

theorem no_double_leak (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hh:HeadData A r U w)
    (h8:treeSpace A 8=pBand A ⊔ chain (diag (nodes A)) U w (r+3))
    (h9:treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U w (r+4))
    (h9r:finrank K (treeSpace A 9)=16)
    {v:Vec K (s+1)} (hv:v∈endZero A 8 i) (hcv:diag (nodes A) v∈endZero A 8 i) :
    v∈chain (diag (nodes A)) U w (r+3) := by
  exact (no_double_leak_both ha ho hs hi hl hh h8 h9 h9r hv hcv).1

end RKCert.Paired.OrderTwelve

