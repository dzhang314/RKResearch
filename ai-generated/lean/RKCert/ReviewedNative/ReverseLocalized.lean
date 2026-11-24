module
public import RKCert.ReviewedNative.ReverseLocalizedInputs

@[expose] public section

/-! # Neutral native reverse rank-one obstruction
All physical chart assumptions are about the genuine native adjoint flag.
The reused scalar/causal gate knows only endomorphisms, clocks and rows. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module RKCert.Endpoint RKCert.OneEscape RKCert.ReverseTwoNode
open RKCert.Paired.OrderTwelve (ReverseRows powerWeight reduce_reverse_rows)
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}

structure LocalizedReverseChart (A : Matrix (Fin s) (Fin s) K) (b : (Fin s→K)) : Prop where
  first : back A b 1=K ∙ normalizedResidual A b 1
  support : ∃ a : K, a≠0 ∧ ∀ i, reflectedClock A i≠a → normalizedResidual A b 1 i=0
  next_out : mat A.transpose (normalizedResidual A b 1)∉back A b 1
  chart : ∀ n≤3, back A b (n+1)=
    chain (diag (reflectedClock A)) (K ∙ normalizedResidual A b 1) (mat A.transpose (normalizedResidual A b 1)) n
  cubic : normalizedResidual A b 2∈back A b 2
  quartic : normalizedResidual A b 3∈back A b 3

variable [CharZero K]
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

omit [CharZero K] in
private theorem short_reverse_join {U Z : Submodule K ((Fin s→K))} {T : (Fin s→K) →ₗ[K] (Fin s→K)}
    (hu : U≤Z) (ht : U.map T≤Z) (hne : ¬U.map T≤U)
    (hr : finrank K Z≤finrank K U+1) : Z=U⊔U.map T := by
  symm; apply Submodule.eq_of_le_of_finrank_le (sup_le hu ht)
  have hlt : U < U⊔U.map T := lt_of_le_of_ne le_sup_left (fun he => hne (le_trans le_sup_right he.ge))
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem localized_reverse_chart_of_ranks (ha:∀i j,i≤j → A i j=0) (ho:HasOrder p A b)
    (hp:2≤p) (seedZero:firstSeed A b=0)
    (ranks:∀n≤4,finrank K (back A b n)=n)
    (nc2:¬(back A b 2).map (diag (reflectedClock A))≤back A b 2)
    (nc3:¬(back A b 3).map (diag (reflectedClock A))≤back A b 3)
    (hcubic:normalizedResidual A b 2∈back A b 2)
    (hquartic:normalizedResidual A b 3∈back A b 3)
    (hc:(back A b 1).map (diag (reflectedClock A))≤back A b 1) : LocalizedReverseChart A b := by
  let d := normalizedResidual A b 1
  let U := K ∙ d
  let N := mat A.transpose
  let Y := diag (reflectedClock A)
  let g := N d
  let B := back A b
  have s0 : B 0=⊥ := by
    change Submodule.span K {firstSeed A b}=⊥
    rw [seedZero,Submodule.span_zero_singleton]
  have du : U=K ∙ quadraticSeed A b := by
    change (K ∙ ((2:K)⁻¹ • quadraticSeed A b))=_
    rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num))]
  have s1 : B 1=U := by
    change B 0 ⊔ (B 0).map N ⊔ (B 0).map Y ⊔ (K ∙ quadraticSeed A b)=U
    rw [s0,du]; simp
  have hcy : U.map Y≤U := s1 ▸ hc
  have line (w : (Fin (s+1)→K)) : (K ∙ w).map N = K ∙ N w := by
    rw [Submodule.map_span,Set.image_singleton]
  have s2 : B 2=U⊔(K ∙ g) := by
    change B 1 ⊔ (B 1).map N ⊔ (B 1).map Y ⊔ (K ∙ quadraticSeed A b)=_
    rw [s1,←du,show U.map N=K ∙ g from line d]
    exact le_antisymm (sup_le (sup_le le_rfl (hcy.trans le_sup_left)) le_sup_left) (le_sup_left.trans le_sup_left)
  have hgrank := ranks 2 (by decide)
  have hdrank := ranks 1 (by decide)
  change finrank K (B 2)=2 at hgrank
  change finrank K (B 1)=1 at hdrank
  have hgn : g∉U := by
    intro hg
    have hr : B 2=B 1 := by rw [s2,s1,sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr hg)]
    rw [hr,hdrank] at hgrank
    contradiction
  have echelon (n : ℕ) (hn : n≤3) :
      B (n+1)=chain Y U g n := by
    obtain ⟨bn,bn2⟩ := (show (¬ (B 2).map Y≤B 2) ∧ (¬ (B 3).map Y≤B 3) from
      ⟨nc2,nc3⟩)
    have step (k : ℕ) (hk : k=2 ∨ k=3) : B (k+1)=B k ⊔ (B k).map Y := by
      apply short_reverse_join (adjointFlag_le_succ (A:=A) (b:=b) (pairCredit A b) k) (adjointFlag_clock (A:=A) (b:=b) (pairCredit A b) k)
      · rcases hk with rfl|rfl <;> assumption
      · have a := ranks k (by omega)
        have e := ranks (k+1) (by omega)
        change finrank K (back A b (k+1))≤finrank K (back A b k)+1
        omega
    induction n with
    | zero => exact s1
    | succ n ih =>
      by_cases hz : n=0
      · subst n; simpa [chain] using s2
      · have ek : n+1=2 ∨ n+1=3 := by omega
        rw [step _ ek,ih (by omega),clock_chain_next hcy (by omega)]
  have hdU : d∈U := Submodule.mem_span_singleton_self _
  obtain ⟨a,hae⟩ := Submodule.mem_span_singleton.mp (hcy (Submodule.mem_map_of_mem hdU))
  have loc (i) (hn : reflectedClock A i≠a) : d i=0 := by
    have h := congrFun hae i
    change a*d i=reflectedClock A i*d i at h
    exact (mul_eq_zero.mp (show (a-reflectedClock A i)*d i=0 by rw [sub_mul,h,sub_self])).resolve_left
      (sub_ne_zero.mpr hn.symm)
  obtain ⟨i,hi,_,_,_,hdi⟩ := greatest_reflected_pivot ha ho hp
  have ha0 : a≠0 := by
    intro hz
    exact hdi (loc i (hz ▸ hi))
  exact ⟨s1,⟨a,ha0,loc⟩,by change g∉B 1;rw [s1];exact hgn,echelon,hcubic,hquartic⟩

omit [CharZero K] in
private theorem short_chart_coeff_one {y d g v : (Fin s→K)}
    (hv : v∈chain (diag y) (K ∙ d) g 1) :
    ∃ a b : K, ∀ i, v i=a*d i+b*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,fun i => by simp⟩

omit [CharZero K] in
private theorem short_chart_coeff_two {y d g v : (Fin s→K)}
    (hv : v∈chain (diag y) (K ∙ d) g 2) :
    ∃ a b c : K, ∀ i, v i=a*d i+(b+c*y i)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,hx⟩ := short_chart_coeff_one hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,fun i => by simp [hx]; ring⟩

omit [CharZero K] in
private theorem short_chart_coeff_three {y d g v : (Fin s→K)}
    (hv : v∈chain (diag y) (K ∙ d) g 3) :
    ∃ a b c e : K, ∀ i, v i=a*d i+(b+c*y i+e*(y i)^2)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,c,hx⟩ := short_chart_coeff_two hx
  obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,e,fun i => by simp [hx]; ring⟩

theorem localized_reverse_rows_of_chart (ha:∀i j,i≤j → A i j=0) (ho:HasOrder p A b)
    (hp:2≤p) (seedZero:firstSeed A b=0) (H:LocalizedReverseChart A b) :
    ∃ a:K,a≠0∧ReverseRows (mat A.transpose) (reflectedClock A) b
      (normalizedResidual A b 1) (mat A.transpose (normalizedResidual A b 1)) a := by
  let N := mat A.transpose
  let y := reflectedClock A
  let d := normalizedResidual A b 1
  let g := N d
  let B := back A b
  let Y := diag y
  obtain ⟨a,ha0,hloc⟩ := H.support
  obtain ⟨j,hy,hb,hbefore,hdi,hnj⟩ := greatest_reflected_pivot ha ho hp
  have hya : y j=a := by by_contra h; exact hnj (hloc j h)
  have pw (k : ℕ) (hk : 0<k) (i : Fin (s+1)) (hi : j < i) : powerWeight y b k i=0 := by
    have h := hbefore i hi
    rcases mul_eq_zero.mp h with h|h
    · change (reflectedClock A i)^k*b i=0; rw [h,zero_pow (by omega),zero_mul]
    · simp [powerWeight,h]
  have pn (k : ℕ) (hk : 0<k) (i : Fin (s+1)) (hi : j ≤ i) : N (powerWeight y b k) i=0 :=
    causal_transpose ha i _ (fun t h => pw k hk t (lt_of_le_of_lt hi (Fin.rev_lt_rev.mp h)))
  have primitive (k : ℕ) (i : Fin (s+1)) :
      N (powerWeight y b k) i = y i^(k+1)*b i/((k+1:ℕ):K)+normalizedResidual A b k i := by
    have h := normalized_residual_apply A b k i
    change normalizedResidual A b k i=N (powerWeight y b k) i-y i^(k+1)*b i/((k+1:ℕ):K) at h
    rw [h]
    ring
  have hd0 (i : Fin (s+1)) (hi : j < i) : d i=0 := by
    have he := primitive 1 i
    have hz := pw 2 (by decide) i hi
    change y i^2*b i=0 at hz
    rw [pn 1 (by decide) _ hi.le,hz,zero_div,zero_add] at he
    exact he.symm
  have hg0 (i : Fin (s+1)) (hi : j ≤ i) : g i=0 :=
    causal_transpose ha i d (fun t h=>hd0 t (lt_of_le_of_lt hi (Fin.rev_lt_rev.mp h)))
  have hng : N g j=0 := causal_transpose ha _ _ (fun _ h=>hg0 _ (Fin.rev_lt_rev.mp h).le)
  have hnyg : N (Y g) j=0 := causal_transpose ha _ _ (fun _ h=>by
    change _*g _=0; rw [hg0 _ (Fin.rev_lt_rev.mp h).le,mul_zero])
  have lc := H.cubic
  have lq := H.quartic
  rw [H.chart 1 (by decide)] at lc
  rw [H.chart 2 (by decide)] at lq
  obtain ⟨c₀,c₁,cc⟩ := short_chart_coeff_one lc
  obtain ⟨q₀,q₁,q₂,qq⟩ := short_chart_coeff_two lq
  have hg2 : g∈B 2 := adjointFlag_transpose (A:=A) (b:=b) (pairCredit A b) 1 (Submodule.mem_map_of_mem (by
    change d∈back A b 1
    rw [H.first]; exact Submodule.mem_span_singleton_self _))
  have ng3 : N g∈B 3 := adjointFlag_transpose (A:=A) (b:=b) (pairCredit A b) 2 (Submodule.mem_map_of_mem hg2)
  have yg3 : Y g∈B 3 := adjointFlag_clock (A:=A) (b:=b) (pairCredit A b) 2 (Submodule.mem_map_of_mem hg2)
  have ng4 : N (Y g)∈B 4 := adjointFlag_transpose (A:=A) (b:=b) (pairCredit A b) 3 (Submodule.mem_map_of_mem yg3)
  change _∈back A b 3 at ng3
  change _∈back A b 4 at ng4
  rw [H.chart 2 (by decide)] at ng3
  rw [H.chart 3 (by decide)] at ng4
  obtain ⟨n₀,n₁,n₂,nn⟩ := short_chart_coeff_two ng3
  obtain ⟨p₀,p₁,p₂,p₃,pp⟩ := short_chart_coeff_three ng4
  change ∀ i, normalizedResidual A b 2 i=c₀*d i+c₁*g i at cc
  change ∀ i, normalizedResidual A b 3 i=q₀*d i+(q₁+q₂*y i)*g i at qq
  change ∀ i, N g i=n₀*d i+(n₁+n₂*y i)*g i at nn
  change ∀ i, N (Y g) i=p₀*d i+(p₁+p₂*y i+p₃*y i^2)*g i at pp
  change d j= -((2:K)⁻¹)* (y j)^2*b j at hdi
  have c₀e : c₀=2*a/3 := by
    apply mul_right_cancel₀ hnj
    have e := primitive 2 j
    rw [pn _ (by decide) _ le_rfl,cc,hg0 _ le_rfl,mul_zero,add_zero] at e
    change 0=y j^3*b j/3+c₀*d j at e
    change c₀*d j=(2*a/3)*d j
    calc c₀*d j = -(y j^3*b j/3) := by linear_combination -e
         _ = _ := by rw [hdi,hya]; ring
  have q₀e : q₀=a^2/2 := by
    apply mul_right_cancel₀ hnj
    have e := primitive 3 j
    rw [pn _ (by decide) _ le_rfl,qq,hg0 _ le_rfl,mul_zero,add_zero] at e
    change 0=y j^4*b j/4+q₀*d j at e
    change q₀*d j=(a^2/2)*d j
    calc q₀*d j = -(y j^4*b j/4) := by linear_combination -e
         _ = _ := by rw [hdi,hya]; ring
  have n₀e : n₀=0 := by
    have e:=nn j; rw [hng,hg0 _ le_rfl,mul_zero,add_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hnj
  have p₀e : p₀=0 := by
    have e:=pp j; rw [hnyg,hg0 _ le_rfl,mul_zero,add_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hnj
  refine ⟨a,ha0,hloc,first_zero_eq_transpose seedZero,rfl,fun i => primitive 1 i,⟨c₁,?_⟩,
    ⟨q₁,q₂,?_⟩,⟨n₁,n₂,?_⟩,⟨p₁,p₂,p₃,?_⟩⟩
  · intro i
    calc N (powerWeight y b 2) i = _ := primitive 2 i
         _ = _ := by rw [cc,c₀e]; ring
  · intro i
    calc N (powerWeight y b 3) i = _ := primitive 3 i
         _ = _ := by rw [qq,q₀e]; ring
  · simpa only [n₀e,zero_mul,zero_add] using nn
  · intro i
    have u : RKCert.Paired.diag y g=diag y g := by
      ext v
      rw [RKCert.Paired.diag_apply,diag_apply]
    change N (RKCert.Paired.diag y g) i=(p₁+p₂*y i+p₃*y i^2)*g i
    rw [u]
    simpa only [p₀e,zero_mul,zero_add] using pp i

theorem localized_reverse_rows_impossible (ha:∀i j,i≤j → A i j=0) (ho:HasOrder p A b)
    (hp:10≤p) (H:∃ a:K,a≠0∧ReverseRows (mat A.transpose) (reflectedClock A) b
      (normalizedResidual A b 1) (mat A.transpose (normalizedResidual A b 1)) a) : False := by
  classical
  obtain ⟨a,ha0,r⟩:=H
  let y := reflectedClock A
  let d := normalizedResidual A b 1
  let g := mat A.transpose d
  let h := powerWeight y b 1+(2/a) • d
  have val (i) : h i=y i*b i+(2/a)*d i := by simp [h,powerWeight]
  have loc (i) (hi : y i≠a) : d i=0 := r.support i hi
  have rz : ∀i,y i=0→h i=0 := by
    intro i hi
    rw [val,loc i (by rw [hi]; exact ha0.symm),hi]; ring
  apply two_node_confinement Fin.revPerm (mat A.transpose) (causal_transpose ha) y h
    (a⁻¹ • g) (reduce_reverse_rows ha0 r) rz
  intro t u
  let T : Finset K := {0,a,t,u}
  have card : T.card≤4 := calc
    T.card ≤ ({a,t,u}:Finset K).card+1 := Finset.card_insert_le ..
    _ ≤ (({t,u}:Finset K).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) _
    _ ≤ ((({u}:Finset K).card+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le ..) _) _
    _ = 4 := by simp
  obtain ⟨i,bi,hi⟩ := reflected_live_avoid ho T (by omega)
  have hh : y i≠0 ∧ y i≠a ∧ y i≠t ∧ y i≠u := by
    change y i∉({0,a,t,u}:Finset K) at hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
  exact ⟨i,by rw [val,loc i hh.2.1,mul_zero,add_zero]; exact mul_ne_zero hh.1 bi,hh.2.2⟩



/-- No localized one-dimensional quadratic reverse line can sustain
the three following paid native ranks and the two extra monomial rows. -/
theorem localized_native_reverse_impossible (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 10≤p) (seedZero : firstSeed A b=0)
    (ranks : ∀n≤4,finrank K (back A b n)=n)
    (nc2 : ¬(back A b 2).map (diag (reflectedClock A))≤back A b 2)
    (nc3 : ¬(back A b 3).map (diag (reflectedClock A))≤back A b 3)
    (h2 : normalizedResidual A b 2∈back A b 2)
    (h3 : normalizedResidual A b 3∈back A b 3) :
    ¬(back A b 1).map (diag (reflectedClock A))≤back A b 1 := by
  intro stable
  have C := localized_reverse_chart_of_ranks ha ho (by omega) seedZero ranks nc2 nc3 h2 h3 stable
  exact localized_reverse_rows_impossible ha ho pay
    (localized_reverse_rows_of_chart ha ho (by omega) seedZero C)

end
end RKResearch.Certified.Graded.Reverse
