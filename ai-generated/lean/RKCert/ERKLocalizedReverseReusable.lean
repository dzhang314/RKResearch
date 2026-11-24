module
public import RKCert.OrderTwelveReverseObstruction

@[expose] public section

/-! # The physical local quadratic reverse obstruction, independent of order twelve
The checked p12 two-node chronology now accepts a true rank/range certificate
from any affordable order. This allows, in particular, the marked p13 prefix
to use the same obstruction without assuming the terminal row was deleted.
-/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.OneEscape RKCert.Endpoint RKCert.ReverseTwoNode Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

omit [CharZero K] in
private theorem short_reverse_join {U Z : Submodule K (Vec K s)} {T : Vec K s →ₗ[K] Vec K s}
    (hu : U≤Z) (ht : U.map T≤Z) (hne : ¬U.map T≤U)
    (hr : finrank K Z≤finrank K U+1) : Z=U⊔U.map T := by
  symm; apply Submodule.eq_of_le_of_finrank_le (sup_le hu ht)
  have hlt : U < U⊔U.map T := lt_of_le_of_ne le_sup_left (fun he => hne (le_trans le_sup_right he.ge))
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem localized_reverse_chart_of_ranks (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:2≤p) (seedZero:backSeed1 A b=0)
    (ranks:∀n≤4,finrank K (back A b n)=n)
    (nc2:¬(back A b 2).map (diag (mirror A))≤back A b 2)
    (nc3:¬(back A b 3).map (diag (mirror A))≤back A b 3)
    (hcubic:reverseResidual A b 2∈back A b 2)
    (hquartic:reverseResidual A b 3∈back A b 3)
    (hc:(back A b 1).map (diag (mirror A))≤back A b 1) : LocalizedReverseChart A b := by
  let d := reverseResidual A b 1
  let U := K ∙ d
  let N := transMat A
  let Y := diag (mirror A)
  let g := N d
  let B := back A b
  have s0 : B 0=⊥ := by
    change Submodule.span K {backSeed1 A b}=⊥
    rw [seedZero,Submodule.span_zero_singleton]
  have du : U=K ∙ backSeed2 A b := by
    change (K ∙ ((2:K)⁻¹ • reflected A b 1))=_
    rw [reflected_one_seed,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num))]
  have s1 : B 1=U := by
    change B 0 ⊔ (B 0).map N ⊔ (B 0).map Y ⊔ (K ∙ backSeed2 A b)=U
    rw [s0,du]; simp
  have hcy : U.map Y≤U := s1 ▸ hc
  have line (w : Vec K (s+1)) : (K ∙ w).map N = K ∙ N w := by
    rw [Submodule.map_span,Set.image_singleton]
  have s2 : B 2=U⊔(K ∙ g) := by
    change B 1 ⊔ (B 1).map N ⊔ (B 1).map Y ⊔ (K ∙ backSeed2 A b)=_
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
      apply short_reverse_join (back_le_succ A b k) (back_map_clock A b k)
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
        rw [step _ ek,ih (by omega),chain_sup_map hcy (by omega)]
  have hdU : d∈U := Submodule.mem_span_singleton_self _
  obtain ⟨a,hae⟩ := Submodule.mem_span_singleton.mp (hcy (Submodule.mem_map_of_mem hdU))
  have loc (i) (hn : mirror A i≠a) : d i=0 := by
    have h := congrFun hae i
    change a*d i=mirror A i*d i at h
    exact (mul_eq_zero.mp (show (a-mirror A i)*d i=0 by rw [sub_mul,h,sub_self])).resolve_left
      (sub_ne_zero.mpr hn.symm)
  obtain ⟨i,hi,_,_,_,hdi⟩ := reverse_first_pivot ha ho hp
  have ha0 : a≠0 := by
    intro hz
    exact hdi (loc i (hz ▸ hi))
  exact ⟨s1,⟨a,ha0,loc⟩,by change g∉B 1;rw [s1];exact hgn,echelon,hcubic,hquartic⟩

omit [CharZero K] in
private theorem short_chart_coeff_one {y d g v : Vec K s}
    (hv : v∈chain (diag y) (K ∙ d) g 1) :
    ∃ a b : K, ∀ i, v i=a*d i+b*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,fun i => by simp⟩

omit [CharZero K] in
private theorem short_chart_coeff_two {y d g v : Vec K s}
    (hv : v∈chain (diag y) (K ∙ d) g 2) :
    ∃ a b c : K, ∀ i, v i=a*d i+(b+c*y i)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,hx⟩ := short_chart_coeff_one hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,fun i => by simp [hx]; ring⟩

omit [CharZero K] in
private theorem short_chart_coeff_three {y d g v : Vec K s}
    (hv : v∈chain (diag y) (K ∙ d) g 3) :
    ∃ a b c e : K, ∀ i, v i=a*d i+(b+c*y i+e*(y i)^2)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,c,hx⟩ := short_chart_coeff_two hx
  obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,e,fun i => by simp [hx,Clock.pow_diag_apply]; ring⟩

theorem localized_reverse_rows_of_chart (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:2≤p) (seedZero:backSeed1 A b=0) (H:LocalizedReverseChart A b) :
    ∃ a:K,a≠0∧ReverseRows (transMat A) (mirror A) b
      (reverseResidual A b 1) (transMat A (reverseResidual A b 1)) a := by
  let N := transMat A
  let y := mirror A
  let d := reverseResidual A b 1
  let g := N d
  let B := back A b
  let Y := diag y
  obtain ⟨a,ha0,hloc⟩ := H.support
  obtain ⟨j,hy,hb,hbefore,hdi,hnj⟩ := reverse_first_pivot ha ho hp
  have hya : y j=a := by by_contra h; exact hnj (hloc j h)
  have pw (k : ℕ) (hk : 0<k) (i : Fin (s+1)) (hi : j < i) : powerWeight y b k i=0 := by
    have h := hbefore i hi
    rcases mul_eq_zero.mp h with h|h
    · change (mirror A i)^k*b i=0; rw [h,zero_pow (by omega),zero_mul]
    · simp [powerWeight,h]
  have pn (k : ℕ) (hk : 0<k) (i : Fin (s+1)) (hi : j ≤ i) : N (powerWeight y b k) i=0 :=
    causal_transpose ha i _ (fun t h => pw k hk t (lt_of_le_of_lt hi (Fin.rev_lt_rev.mp h)))
  have primitive (k : ℕ) (i : Fin (s+1)) :
      N (powerWeight y b k) i = y i^(k+1)*b i/((k+1:ℕ):K)+reverseResidual A b k i := by
    rw [reverseResidual_eq A b k (Nat.cast_ne_zero.mpr (by omega))]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,reflWeight_power]
    change N (powerWeight y b k) i = _ + (N (powerWeight y b k) i-_*powerWeight y b (k+1) i)
    rw [show powerWeight y b (k+1) i=y i^(k+1)*b i from rfl,div_eq_mul_inv]
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
  have hg2 : g∈B 2 := back_map_transpose A b 1 (Submodule.mem_map_of_mem (by
    rw [H.first]; exact Submodule.mem_span_singleton_self _))
  have ng3 : N g∈B 3 := back_map_transpose A b 2 (Submodule.mem_map_of_mem hg2)
  have yg3 : Y g∈B 3 := back_map_clock A b 2 (Submodule.mem_map_of_mem hg2)
  have ng4 : N (Y g)∈B 4 := back_map_transpose A b 3 (Submodule.mem_map_of_mem yg3)
  change _∈back A b 3 at ng3
  change _∈back A b 4 at ng4
  rw [H.chart 2 (by decide)] at ng3
  rw [H.chart 3 (by decide)] at ng4
  obtain ⟨n₀,n₁,n₂,nn⟩ := short_chart_coeff_two ng3
  obtain ⟨p₀,p₁,p₂,p₃,pp⟩ := short_chart_coeff_three ng4
  change ∀ i, reverseResidual A b 2 i=c₀*d i+c₁*g i at cc
  change ∀ i, reverseResidual A b 3 i=q₀*d i+(q₁+q₂*y i)*g i at qq
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
  refine ⟨a,ha0,hloc,sub_eq_zero.mp seedZero,rfl,fun i => primitive 1 i,⟨c₁,?_⟩,
    ⟨q₁,q₂,?_⟩,⟨n₁,n₂,?_⟩,⟨p₁,p₂,p₃,?_⟩⟩
  · intro i
    calc N (powerWeight y b 2) i = _ := primitive 2 i
         _ = _ := by rw [cc,c₀e]; ring
  · intro i
    calc N (powerWeight y b 3) i = _ := primitive 3 i
         _ = _ := by rw [qq,q₀e]; ring
  · simpa only [n₀e,zero_mul,zero_add] using nn
  · simpa only [p₀e,zero_mul,zero_add] using pp

theorem localized_reverse_rows_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:10≤p) (H:∃ a:K,a≠0∧ReverseRows (transMat A) (mirror A) b
      (reverseResidual A b 1) (transMat A (reverseResidual A b 1)) a) : False := by
  classical
  obtain ⟨a,ha0,r⟩:=H
  let y := mirror A
  let d := reverseResidual A b 1
  let g := transMat A d
  let h := powerWeight y b 1+(2/a) • d
  have val (i) : h i=y i*b i+(2/a)*d i := by simp [h,powerWeight]
  have loc (i) (hi : y i≠a) : d i=0 := r.support i hi
  have rz : ∀i,y i=0→h i=0 := by
    intro i hi
    rw [val,loc i (by rw [hi]; exact ha0.symm),hi]; ring
  apply two_node_confinement Fin.revPerm (transMat A) (causal_transpose ha) y h
    (a⁻¹ • g) (reduce_reverse_rows ha0 r) rz
  intro t u
  let T : Finset K := {0,a,t,u}
  have card : T.card≤4 := calc
    T.card ≤ ({a,t,u}:Finset K).card+1 := Finset.card_insert_le ..
    _ ≤ (({t,u}:Finset K).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) _
    _ ≤ ((({u}:Finset K).card+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le ..) _) _
    _ = 4 := by simp
  obtain ⟨i,bi,hi⟩ := reflected_active_avoid ho T (by omega)
  have hh : y i≠0 ∧ y i≠a ∧ y i≠t ∧ y i≠u := by
    change y i∉({0,a,t,u}:Finset K) at hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
  exact ⟨i,by rw [val,loc i hh.2.1,mul_zero,add_zero]; exact mul_ne_zero hh.1 bi,hh.2.2⟩

end RKCert.Paired.OrderTwelve
