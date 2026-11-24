module
public import RKCert.DirkCubicSignedBudget
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.Endpoint Polynomial RKCert.OneEscape
open scoped Classical
variable {K:Type*} [Field K] {s p:ℕ}
noncomputable section
/-- Only terminal-zero words, not the full marked spaces, are needed for
the signed cubic rank. Genuine transpose and primitive residues vanish
there because the actual terminal column is zero and its clock is one. -/
theorem signed_cubic_deleted_sites {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [CharZero K] {H j:ℕ}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (D:PaidReverseBand A b p H)
    (jl:3≤j) (jh:j+1≤H) (mass:∀a:K,combinedMass (mirror A) (tau A b) a=0):
    j-2+j/2≤(Clock.headSites (mirror A) (tau A b)).card:=by
  have paid:=D.paid
  classical
  let c:=mirror A
  let τ:=tau A b
  let S:=Clock.headSites c τ
  let T:=S.image (fun z=>Clock.fiber c z τ)
  let U:=Submodule.span K (T:Set (Vec K (s+1)))
  have sub(a:K)(ha:a∈S):Clock.fiber c a τ∈U:=Submodule.subset_span (Finset.mem_image_of_mem _ ha)
  have inv:U.map (diag c)≤U:=by
    apply Submodule.map_le_iff_le_comap.mpr;apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp (show v∈T from hv)
    have eqn:diag c (Clock.fiber c z τ)=z • Clock.fiber c z τ:=by
      ext i;by_cases hit:c i=z <;>simp [Clock.fiber,hit]
    change diag c (Clock.fiber c z τ)∈U
    rw [eqn];exact U.smul_mem _ (sub z hz)
  have high:U≤marked A p p:=by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp (show v∈T from hv)
    apply leaf_zero_high_marked
    rw [row_apply];simp only [Clock.fiber,Pi.one_apply,mul_one]
    rw [←Finset.sum_filter];exact mass z
  have whole(j:ℕ)(lo:3≤j)(hi:j≤H):ReverseHermite.zeroMarked A p (Fin.last s) j≤U:=by
    rw [D.cover j (by omega) hi,D.nonlocal_words ha ho (D.nonlocal_cubic ha ho) (by omega) (by omega)]
    apply (chain_le_iff _).mpr
    refine ⟨bot_le,fun k _=>?_⟩
    have eqn:(diag c^k) τ=∑z∈S,z^k • Clock.fiber c z τ:=by
      ext i;rw [Clock.pow_diag_apply,Finset.sum_apply]
      by_cases nz:τ i≠0
      · rw [Finset.sum_eq_single_of_mem (c i) (Clock.headSites_mem i nz)]
        · simp [Clock.fiber]
        · intro z _ off;simp [Clock.fiber,Ne.symm off]
      · have zz:τ i=0:=not_not.mp nz
        simp [Clock.fiber,zz]
    rw [eqn];exact U.sum_mem (fun z hz=>U.smul_mem _ (sub z hz))
  have inc:=ReverseHermite.incoming ha ho (r:=j/2) (by omega) high inv (whole j jl (by omega))
    (fun v hv=>whole (j+1) (by omega) jh ⟨marked_mat (show j+2≤p by omega) hv.1,ReverseHermite.trans_terminal _ D.col v⟩)
    (fun P deg=>whole (j+1) (by omega) jh (ReverseHermite.terminal_primitive ho (j:=j) (by omega) (Fin.last s) D.terminal D.col P (by omega)))
  have rank:finrank K (ReverseHermite.zeroMarked A p (Fin.last s) j)=j-2:=by rw [D.cover j (by omega) (by omega)];exact D.rank (by omega)
  rw [rank] at inc
  exact inc.trans ((finrank_span_finset_le_card T).trans Finset.card_image_le)

theorem double_support_of_zero_mass (c v:Vec K s) (zero:∀a:K,combinedMass c v a=0):
    2*(Clock.headSites c v).card≤(Finset.univ.filter fun i=>v i≠0).card:=by
  classical
  let I:=Finset.univ.filter fun i=>v i≠0
  let S:=I.image c
  have fiber (a:K) (ha:a∈S):2≤(I.filter fun t=>c t=a).card:=by
    by_contra! small
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    have nz:v i≠0:=(Finset.mem_filter.mp hi).2
    have mass:=zero (c i)
    rw [combinedMass,Finset.sum_eq_single i] at mass
    · exact nz mass
    · intro j hj ne
      by_contra m
      have eq:=Finset.card_le_one.mp (by omega:(I.filter fun t=>c t=c i).card≤1) j
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,m⟩,(Finset.mem_filter.mp hj).2⟩)
        i (Finset.mem_filter.mpr ⟨hi,rfl⟩)
      exact ne eq
    · intro hh;exact False.elim (hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩))
  change 2*S.card≤I.card
  calc
    _=∑_a∈S,2:=by simp [Nat.mul_comm]
    _≤∑a∈S,(I.filter fun t=>c t=a).card:=Finset.sum_le_sum fiber
    _=I.card:=(Finset.card_eq_sum_card_image c I).symm

/-- Sharp parity-safe signed support count. Unlike flooring the number
of available paired observations, the odd budget earns an unpaired
extra row when there are already sufficiently many different sites. -/
theorem signed_cubic_sharp_physical {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [CharZero K] {H j:ℕ}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (D:PaidReverseBand A b p H)
    (jl:3≤j) (jh:j+1≤H):
    min (p-2) (2*(j-2+j/2))≤(Finset.univ.filter (fun i=>tau A b i≠0)).card:=by
  classical
  have ph:=D.paid;have lo:=D.low
  have mom(P:K[X])(deg:P.natDegree≤p-4):(∑i,tau A b i*P.eval (mirror A i))=0:=by
    have tm:tau A b∈marked A p 3:=seed3_marked ho (by omega)
    have ev:=evalNodes_mem_treeSpace A (reflectPolynomial P) ((reflectPolynomial_degree P).trans deg)
    have val:=mem_annih.mp tm _ (show evalNodes A (reflectPolynomial P)∈treeSpace A (p-1-3) from (show p-1-3=p-4 by omega) ▸ ev)
    simpa only [row_apply,evalNodes_apply,reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X,mirror,Pi.sub_apply,Pi.one_apply] using val
  let S:=Clock.headSites (mirror A) (tau A b)
  by_cases many:p-2≤S.card
  · exact (min_le_left ..).trans (many.trans Finset.card_image_le)
  have masses:=nodal_mass_zero_of_paid (n:=p-4) (mirror A) (tau A b) (by change S.card≤_;omega) mom
  have big:=signed_cubic_deleted_sites ha ho D jl jh masses
  have double:=double_support_of_zero_mass (mirror A) (tau A b) masses
  exact (min_le_right ..).trans ((Nat.mul_le_mul_left 2 big).trans double)
end
end RKCert.Paired.Terminal
