module
public import RKCert.ERKOrder13Chart
public import RKCert.ERKLocalizedReverseReusable

@[expose] public section

/-! # The marked order-13 prefix has full E11
The rank-one L2 chronology is the same checked physical argument
as at order 12. Here its exact annihilators are those of Eplus.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.Paired.OrderTwelve RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2000000

omit [CharZero K] in
theorem thirteen_prefix_back_exact (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    {n:ℕ} (n0:1≤n) (n1:n≤4) : back A b n=annih (treePlus A 1 (11-n)) := by
  let j:=11-n
  have wdt:=C.width
  have j0:a+1≤j := by dsimp [j];omega
  have j1:j≤10 := by dsimp [j];omega
  have eq : j+n+2=13 := by dsimp [j];omega
  have i : back A b n≤annih (treePlus A 1 j) := by
    intro w hw
    apply mem_annih.mpr
    change treePlus A 1 j≤(row w).ker
    unfold treePlus
    exact sup_le (mem_annih.mp (back_annih ho j n (by omega) hw))
      (mem_annih.mp (M.backTail n hw))
  apply Submodule.eq_of_le_of_finrank_le i
  have df := backward_exact_dim (treePlus A 1 j)
  have r := C.rich j j0 j1
  have b := back_finrank ha ho n (by omega)
  have sz:=S.size
  omega

omit [CharZero K] in
theorem forward_clock_from_reflected_annih (E:Submodule K (Vec K (s+1)))
    (h : (annih E).map (diag (mirror A))≤annih E) : E.map (diag (nodes A))≤E := by
  rintro _ ⟨v,hv,rfl⟩
  apply row_annih_test
  intro w hw
  have e : diag (nodes A) w=w-diag (mirror A) w := by ext i;simp [mirror,sub_mul]
  have r : diag (nodes A) w∈annih E := by
    rw [e]
    exact (annih E).sub_mem hw (h (Submodule.mem_map_of_mem hw))
  rw [←row_flip_diag]
  exact mem_annih.mp r v hv

omit [CharZero K] in
theorem reflected_annih_from_forward_clock (E:Submodule K (Vec K (s+1)))
    (h : E.map (diag (nodes A))≤E) : (annih E).map (diag (mirror A))≤annih E := by
  rintro _ ⟨v,hv,rfl⟩
  apply mem_annih.mpr
  intro w hw
  rw [row_flip_diag]
  have e : diag (mirror A) w=w-diag (nodes A) w := by ext i; simp [mirror,sub_mul]
  rw [e]
  exact mem_annih.mp hv _ (E.sub_mem hw (h (Submodule.mem_map_of_mem hw)))

theorem reverse_residual_in_marked_annih (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b 13) (M:Margin A b 6 1 1) {j k:ℕ}
    (hk:k≤3) (hpay:j+k+2≤13) : reverseResidual A b k∈annih (treePlus A 1 j) := by
  let v:=reverseResidual A b k
  have hm : mirror A (Fin.last s)=0 := by
    change 1-nodes A (Fin.last s)=0
    rw [M.atOne (by decide),sub_self]
  have he : v (Fin.last s)=0 := by
    unfold v
    rw [reverseResidual_eq A b k (Nat.cast_ne_zero.mpr (by omega))]
    have h := transMat_vanish ha (Fin.last s) (reflWeight A b k)
      (fun i hi=>False.elim ((not_lt_of_ge (Fin.le_last i)) hi)) (Fin.last s) le_rfl
    change transMat A (reflWeight A b k) (Fin.last s)=0 at h
    rw [Pi.sub_apply,h]
    simp only [Pi.smul_apply,smul_eq_mul,reflWeight_power,powerWeight,
      hm,zero_pow (Nat.succ_ne_zero _),zero_mul,mul_zero,sub_zero]
  apply mem_annih.mpr
  change treePlus A 1 j≤(row v).ker
  unfold treePlus
  apply sup_le (mem_annih.mp (reverseResidual_mem ho hk hpay))
  rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)]
  change Submodule.span K {terminal s} ≤ (row v).ker
  apply (Submodule.span_singleton_le_iff_mem ..).mpr
  change row v (terminal s)=0
  rwa [row_terminal]

theorem thirteen_prefix_back_one_not_invariant (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b 13) (S:Saturated A b 6 1)
    (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G) :
    ¬(back A b 1).map (diag (mirror A))≤back A b 1 := by
  have width:=C.width
  have sz:=S.size
  have ho':HasTreeOrderAtLeast A b (2*6+1) := ho
  have zr : finrank K (back A b 0)=0 := by have:=M.budget;omega
  have seed := seed_zero_of_rank_zero zr
  have exact13 : ∀ n,1≤n→n≤4→back A b n=annih (treePlus A 1 (11-n)) :=
    fun _=>thirteen_prefix_back_exact ha ho S M C
  have ranks (n:ℕ) (hn:n≤4) : finrank K (back A b n)=n := by
    by_cases h:n=0
    · subst n;exact zr
    · rw [exact13 n (by omega) hn]
      have de:=backward_exact_dim (treePlus A 1 (11-n))
      have e:=C.rich (11-n) (by omega) (by omega)
      omega
  have no (j:ℕ) (j0:8≤j) (j1:j≤9) :
      ¬(treePlus A 1 j).map (diag (nodes A))≤treePlus A 1 j := by
    apply edge_noninvariant_short ha ho' (by decide) M (by omega) (by omega)
    · have e:=C.rich j (by omega) (by omega);omega
    · rw [ite_eq_right (by omega)]
      have e:=C.rich (j-1) (by omega) (by omega);omega
  have nc2 : ¬(back A b 2).map (diag (mirror A))≤back A b 2 := by
    rw [exact13 2 (by decide) (by decide)]
    exact fun h=>no 9 (by decide) (by decide) (forward_clock_from_reflected_annih _ h)
  have nc3 : ¬(back A b 3).map (diag (mirror A))≤back A b 3 := by
    rw [exact13 3 (by decide) (by decide)]
    exact fun h=>no 8 (by decide) (by decide) (forward_clock_from_reflected_annih _ h)
  have c2 : reverseResidual A b 2∈back A b 2 := by
    rw [exact13 2 (by decide) (by decide)]
    exact reverse_residual_in_marked_annih ha ho M (by decide) (by decide)
  have c3 : reverseResidual A b 3∈back A b 3 := by
    rw [exact13 3 (by decide) (by decide)]
    exact reverse_residual_in_marked_annih ha ho M (by decide) (by decide)
  intro hC
  have H := localized_reverse_chart_of_ranks ha ho (by decide) seed ranks nc2 nc3 c2 c3 hC
  exact localized_reverse_rows_impossible ha ho (by decide)
    (localized_reverse_rows_of_chart ha ho (by decide) seed H)

theorem thirteen_prefix_exact_eleven (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G) :
    treePlus A 1 11=⊤ ∧ treePlus A 1 11=polyBand A a⊔Band13 A a r U w 11 := by
  have width:=C.width
  have nc : ¬(treePlus A 1 10).map (diag (nodes A))≤treePlus A 1 10 := by
    intro inv
    apply thirteen_prefix_back_one_not_invariant ha ho S M C
    rw [thirteen_prefix_back_exact ha ho S M C (n:=1) (by decide) (by decide)]
    exact reflected_annih_from_forward_clock _ inv
  let V:=treePlus A 1 10⊔(treePlus A 1 10).map (diag (nodes A))
  have hlt : treePlus A 1 10<V := lt_of_le_of_ne le_sup_left
    (fun e=>nc (le_sup_right.trans (le_of_eq e.symm)))
  have hV : V≤treePlus A 1 11 := sup_le (Eplus_mono A 1 (by decide)) (Eplus_clock A 1 10)
  have r10:=C.rich 10 (by omega) (by decide)
  have low:=Submodule.finrank_lt_finrank_of_lt hlt
  have vcap := (Submodule.finrank_le (R:=K) (M:=Vec K (s+1)) V)
  have tcap := Submodule.finrank_le (R:=K) (M:=Vec K (s+1)) (treePlus A 1 11)
  have eq : finrank K (Vec K (s+1))=19 := by simp [Vec,S.size]
  rw [eq] at vcap tcap
  have mid:=Submodule.finrank_mono hV
  have vt : V=treePlus A 1 11 := Submodule.eq_of_le_of_finrank_le hV (by omega)
  refine ⟨Submodule.eq_top_of_finrank_eq (by rw [eq];omega),?_⟩
  have hC := C.chart 10 (by omega) (by decide)
  have e : headLen 6 a r 10+1=headLen 6 a r 11 := by unfold headLen;omega
  rw [←vt]
  unfold V Band13 forwardBand
  rw [←e]
  exact Eplus_band_growth (q:=a) (j:=10) (n:=headLen 6 a r 10) (by omega) (by unfold headLen;omega) C.marked.stable hC

end RKCert.Paired.FiniteMidpoint

