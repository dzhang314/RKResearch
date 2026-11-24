module
public import RKCert.DirkPaidPorts
public import RKCert.DirkEvenPhysicalCount
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.Endpoint Polynomial RKCert.OneEscape
open scoped Classical
variable {K:Type*} [Field K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
noncomputable section

/-- Total signed mass zero is exactly enough for membership in the last
marked test (only the ordinary constant tree); it is not membership in
the much lower marked grade for which the Hermite comparison is used. -/
theorem leaf_zero_high_marked {u:Vec K s} (hz:row u 1=0):u∈marked A p p:=by
  change u∈annih (treeSpace A (p-1-p))
  rw [show p-1-p=0 by omega,mem_annih]
  have inc:treeSpace A 0≤LinearMap.ker (row u):=by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,low,rfl⟩
    cases t with
    | leaf=>exact hz
    | attach t v=>have ht:=t.order_pos;have hv:=v.order_pos;simp only [Tree.order] at low;omega
  exact fun v hv=>inc hv

theorem nodal_mass_zero_of_paid {n : ℕ} (c w : Vec K s)
    (hS : (Clock.headSites c w).card≤n+1)
    (hpay : ∀ P : K[X], P.natDegree≤n → ∑ i,w i*P.eval (c i)=0)
    (a : K) : combinedMass c w a=0 := by
  classical
  let S := Clock.headSites c w
  change S.card≤n+1 at hS
  rw [combinedMass,Finset.sum_filter]
  by_cases ha : a∈S
  · let f (z : K) := if z=a then 1 else (0:K)
    let P := Lagrange.interpolate S id f
    have atSite (z : K) (hz : z∈S) : P.eval z=f z :=
      Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hz
    have hP : P≠0 := by
      intro e
      have zz := atSite a ha
      rw [e] at zz
      simp [f] at zz
    have deg : P.natDegree < S.card := (natDegree_lt_iff_degree_lt hP).mpr
      (Lagrange.degree_interpolate_lt (s:=S) f (Set.injOn_id _))
    calc
      _ = ∑ i,w i*P.eval (c i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : w i=0
        · simp [hi]
        · rw [atSite _ (Clock.headSites_mem i hi)]
          by_cases hz : c i=a <;> simp [f,hz]
      _ = 0 := hpay P (by omega)
  · apply Finset.sum_eq_zero
    intro i _
    by_cases hi : c i=a
    · have he : w i=0 := by
        by_contra hn
        apply ha
        rw [←hi]
        exact Clock.headSites_mem i hn
      simp [hi,he]
    · simp [hi]

/-- A signed cubic orbit occupying full native marked spaces up to H pays
j−2+⌊j/2⌋ distinct knots if its net mass vanishes on every fiber. The
hull is required to be marked only at the constant-tree grade p. -/
theorem signed_cubic_orbit_sites {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [CharZero K] {H j:ℕ}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (D:PaidReverseBand A b p H)
    (words:∀ i : ℕ, 2 ≤ i → i ≤ H → marked A p i = dirkBack A b (i-2))
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
  have whole(j:ℕ)(lo:3≤j)(hi:j≤H):marked A p j≤U:=by
    rw [words j (by omega) hi,D.nonlocal_words ha ho (D.nonlocal_cubic ha ho) (by omega) (by omega)]
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
    (fun v hv=>whole (j+1) (by omega) jh (marked_mat (show j+2≤p by omega) hv))
    (fun P deg=>whole (j+1) (by omega) jh (weighted_reverse_primitive ho (n:=j) (by omega) (by omega)))
  have rank:finrank K (marked A p j)=j-2:=by rw [words j (by omega) (by omega)];exact D.rank (by omega)
  rw [rank] at inc
  exact inc.trans ((finrank_span_finset_le_card T).trans Finset.card_image_le)

theorem signed_cubic_ten_sites {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [CharZero K]
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (D:PaidReverseBand A b 20 9)
    (words:∀j,2≤j→j≤9→marked A 20 j=dirkBack A b (j-2))
    (mass:∀a:K,combinedMass (mirror A) (tau A b) a=0):
    10≤(Clock.headSites (mirror A) (tau A b)).card:=
  signed_cubic_orbit_sites ha ho D words (j:=8) (by decide) (by decide) mass

/-- Uniform signed-cubic physical support budget. Even when distinct
net-mass cancellations occur, each required knot must be paid for by
two physical occupied rows unless there are already 2k distinct knots. -/
theorem signed_cubic_physical_budget {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [CharZero K] {H j k:ℕ}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (D:PaidReverseBand A b p H)
    (words:∀ i : ℕ, 2 ≤ i → i ≤ H → marked A p i = dirkBack A b (i-2))
    (jl:3≤j) (jh:j+1≤H) (basis:k≤j-2+j/2) (pay:2*k+2≤p):
    2*k≤(Finset.univ.filter (fun i=>tau A b i≠0)).card:=by
  have ph:=D.paid;have lo:=D.low
  have mom(P:K[X])(deg:P.natDegree≤p-4):(∑i,tau A b i*P.eval (mirror A i))=0:=by
    have tm:tau A b∈marked A p 3:=seed3_marked ho (by omega)
    have ev:=evalNodes_mem_treeSpace A (reflectPolynomial P) ((reflectPolynomial_degree P).trans deg)
    have val:=mem_annih.mp tm _ (show evalNodes A (reflectPolynomial P)∈treeSpace A (p-1-3) from (show p-1-3=p-4 by omega) ▸ ev)
    simpa only [row_apply,evalNodes_apply,reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X,mirror,Pi.sub_apply,Pi.one_apply] using val
  apply signed_fiber_payment (mirror A) (tau A b) k _ (fun P h=>mom P (by omega))
  by_contra! small
  have masses:=nodal_mass_zero_of_paid (n:=p-4) (mirror A) (tau A b) (by omega) mom
  have huge:=signed_cubic_orbit_sites ha ho D words jl jh masses;omega

/-- Both the many-distinct-atoms and the signed-cancellation alternative
pay eighteen different physical positions. -/
theorem twenty_dirty_eighteen {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [CharZero K]
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (D:PaidReverseBand A b 20 9)
    (words:∀j,2≤j→j≤9→marked A 20 j=dirkBack A b (j-2)) :
    18≤(Finset.univ.filter (fun i=>tau A b i≠0)).card:=by
  exact signed_cubic_physical_budget ha ho D words (j:=8) (k:=9) (by decide) (by decide) (by decide) (by decide)

end
end RKCert.Paired.Terminal
