module
public import RKCert.OrderTwelveReverseLocalized

@[expose] public section
/-! # Actual coefficient identities for a localized reverse line
The degree-three, degree-four, and two outgoing head equations have no
unspecified pure defect left; their leading coefficients are pinned at the
genuine first active reflected node, without assuming nonzero ghost weights.
-/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.OneEscape RKCert.Endpoint Module
variable {K : Type*} [Field K] {s : ℕ}

/-- Zero-weight rows do not create active nodes or count toward this certificate. -/
theorem reflected_active_avoid [CharZero K] {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (T : Finset K) (hs : T.card<p/2) :
    ∃ i, b i≠0 ∧ mirror A i∉T := by
  classical
  by_contra! h
  let c := nodes A
  have hc : activeNonzero c b ⊆ T.image (fun z => 1-z) := by
    intro z hz
    have hn : combinedMass c b z≠0 := (Finset.mem_filter.mp hz).2.2
    obtain ⟨i,he,hi⟩ : ∃i, c i=z ∧ b i≠0 := by
      by_contra! he
      apply hn
      exact Finset.sum_eq_zero (fun i hi => he i (Finset.mem_filter.mp hi).2)
    refine Finset.mem_image.mpr ⟨mirror A i,h i hi,?_⟩
    change 1-(1-c i)=z
    rw [he]; ring
  have a := Finset.card_le_card hc
  have q := activeNonzero_card_of_treeOrder ho
  change p/2≤(activeNonzero c b).card at q
  exact (not_le_of_gt hs) (q.trans (a.trans Finset.card_image_le))

private theorem chart_coeff_one {y d g v : Vec K s}
    (hv : v∈chain (diag y) (K ∙ d) g 1) :
    ∃ a b : K, ∀ i, v i=a*d i+b*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,fun i => by simp⟩

private theorem chart_coeff_two {y d g v : Vec K s}
    (hv : v∈chain (diag y) (K ∙ d) g 2) :
    ∃ a b c : K, ∀ i, v i=a*d i+(b+c*y i)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,hx⟩ := chart_coeff_one hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,fun i => by simp [hx]; ring⟩

private theorem chart_coeff_three {y d g v : Vec K s}
    (hv : v∈chain (diag y) (K ∙ d) g 3) :
    ∃ a b c e : K, ∀ i, v i=a*d i+(b+c*y i+e*(y i)^2)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,c,hx⟩ := chart_coeff_two hx
  obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,e,fun i => by simp [hx,Clock.pow_diag_apply]; ring⟩

/-- Coordinatewise power weighted by v. -/
def powerWeight (y v : Vec K s) (k : ℕ) : Vec K s := fun i => y i^k*v i

theorem reflWeight_power (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ) :
    reflWeight A b k=powerWeight (mirror A) b k := rfl

/-- A single row system, in either orientation. The actual comparison order
enters through the causal operator and the separate pivot statement. -/
structure ReverseRows (N : Vec K s →ₗ[K] Vec K s) (y v d g : Vec K s) (a : K) : Prop where
  support : ∀ i, y i≠a → d i=0
  base : N v=diag y v
  next : N d=g
  quadratic : ∀i, N (powerWeight y v 1) i=y i^2*v i/2+d i
  cubic : ∃ k : K, ∀i, N (powerWeight y v 2) i=y i^3*v i/3+(2*a/3)*d i+k*g i
  quartic : ∃ k l : K, ∀i, N (powerWeight y v 3) i=y i^4*v i/4+a^2/2*d i+(k+l*y i)*g i
  advance : ∃ k l : K, ∀i, N g i=(k+l*y i)*g i
  shifted : ∃ k l m : K, ∀i, N (diag y g) i=(k+l*y i+m*y i^2)*g i

variable [CharZero K]

/-- A physically defined model for all three chronology branches, including
the two clock moments and both outgoing relations at their true costs. -/
theorem localized_reverse_rows {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b)
    (hc : (back A b 1).map (diag (mirror A))≤back A b 1) :
    ∃ a : K, a≠0 ∧ ReverseRows (transMat A) (mirror A) b
      (reverseResidual A b 1) (transMat A (reverseResidual A b 1)) a := by
  let N := transMat A
  let y := mirror A
  let d := reverseResidual A b 1
  let g := N d
  let B := back A b
  let Y := diag y
  have H := localized_reverse_chart ha ho hs hc
  obtain ⟨a,ha0,hloc⟩ := H.support
  obtain ⟨j,hy,hb,hbefore,hdi,hnj⟩ := reverse_first_pivot ha ho (by decide)
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
  obtain ⟨c₀,c₁,cc⟩ := chart_coeff_one lc
  obtain ⟨q₀,q₁,q₂,qq⟩ := chart_coeff_two lq
  have hg2 : g∈B 2 := back_map_transpose A b 1 (Submodule.mem_map_of_mem (by
    rw [H.first]; exact Submodule.mem_span_singleton_self _))
  have ng3 : N g∈B 3 := back_map_transpose A b 2 (Submodule.mem_map_of_mem hg2)
  have yg3 : Y g∈B 3 := back_map_clock A b 2 (Submodule.mem_map_of_mem hg2)
  have ng4 : N (Y g)∈B 4 := back_map_transpose A b 3 (Submodule.mem_map_of_mem yg3)
  change _∈back A b 3 at ng3
  change _∈back A b 4 at ng4
  rw [H.chart 2 (by decide)] at ng3
  rw [H.chart 3 (by decide)] at ng4
  obtain ⟨n₀,n₁,n₂,nn⟩ := chart_coeff_two ng3
  obtain ⟨p₀,p₁,p₂,p₃,pp⟩ := chart_coeff_three ng4
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
  refine ⟨a,ha0,hloc,sub_eq_zero.mp hs.backZero,rfl,fun i => primitive 1 i,⟨c₁,?_⟩,
    ⟨q₁,q₂,?_⟩,⟨n₁,n₂,?_⟩,⟨p₁,p₂,p₃,?_⟩⟩
  · intro i
    calc N (powerWeight y b 2) i = _ := primitive 2 i
         _ = _ := by rw [cc,c₀e]; ring
  · intro i
    calc N (powerWeight y b 3) i = _ := primitive 3 i
         _ = _ := by rw [qq,q₀e]; ring
  · simpa only [n₀e,zero_mul,zero_add] using nn
  · simpa only [p₀e,zero_mul,zero_add] using pp

end RKCert.Paired.OrderTwelve
