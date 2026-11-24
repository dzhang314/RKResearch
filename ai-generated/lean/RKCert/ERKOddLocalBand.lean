module
public import RKCert.ERKOddReverseHorizon
public import RKCert.DirkPolynomialMarked

@[expose] public section
/-! # Paid, genuinely orthogonal one-head chart for a localized linear seed
The ordinary RK annihilator at grade eight is exact; no claim is made
about equality with the reverse primitive flag at grade nine. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.OneEscape RKCert.Endpoint
open Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
noncomputable section

/-- Positive definiteness needs only the coefficient field ordering. -/
theorem dot_split_own_annih {s:ℕ}(U:Submodule K (Vec K s)) : U⊔annih U=⊤:=by
  classical
  have e:U⊓annih U=⊥:=by
    apply le_bot_iff.mp
    intro u hu
    have sm:=mem_annih.mp hu.2 u hu.1
    rw [row_apply] at sm
    have f (i:Fin s):u i=0:=by
      by_contra hz
      have d:u i*u i≤∑j,u j*u j:=
        Finset.single_le_sum (f:=fun j=>u j*u j) (fun j _=>mul_self_nonneg _) (Finset.mem_univ i)
      rw [sm] at d
      exact (not_lt_of_ge d) (mul_self_pos.mpr hz)
    change u=0
    ext i
    exact f i
  apply Submodule.eq_of_le_of_finrank_le le_top
  have pay:=Submodule.finrank_sup_add_finrank_inf_eq U (annih U)
  rw [e,finrank_bot,add_zero,finrank_annih_eq] at pay
  rw [pay,finrank_top,Module.finrank_fin_fun]

variable {A:Fin 26→Fin 26→K}{b:Vec K 26}

structure LocalLinearBand (A:Fin 26→Fin 26→K) (b:Vec K 26)
    (r:ℕ)(U:Submodule K (Vec K 26))(τ:Vec K 26):Prop where
  short:r=1∨r=2
  base:U=primitiveBack A b (r-1)
  dimension:finrank K U=r
  clock:U.map (diag (mirror A))≤U
  orthogonal:τ∈annih U
  paid:τ∈annih (treeSpace A (15-r))
  sites:9-r≤(headSites (mirror A) τ).card
  flags:∀n,r≤n→n≤7→primitiveBack A b n=chain (diag (mirror A)) U τ (n+1-r)
  full:annih (treeSpace A 8)=chain (diag (mirror A)) U τ (8-r)

set_option maxHeartbeats 2700000 in
theorem odd17_local_linear_band (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (S:OddBalanced (s:=25) A b 8)(nz:backSeed1 A b≠0)
    (few:(orbitSites (mirror A) (backSeed1 A b)).card≤2):
    ∃r:ℕ,∃U:Submodule K (Vec K 26),∃τ:Vec K 26,LocalLinearBand A b r U τ:=by
  classical
  let L:=primitiveBack A b
  let y:=mirror A
  let C:=diag y
  let d:=backSeed1 A b
  have mono:Monotone L:=monotone_nat_of_le_succ primitiveBack_le_succ
  have od:finrank K (back A b 0)=1:=finrank_span_singleton nz
  have ranks(n:ℕ)(h:n≤7):finrank K (L n)=n+1:=by
    change finrank K (primitiveBack A b n)=_
    rw [←(S.flags n h).2,(S.flags n h).1,od]
  have esc(n:ℕ)(a:2≤n)(g:n≤7):¬(L n).map C≤L n:=
    balanced_odd_reverse_gap ha ho (by decide) (by decide) S n a g
  let r:=if (L 1).map C≤L 1 then 2 else 1
  have rs:r=1∨r=2:=by dsimp [r];split <;> simp
  let U:=L (r-1)
  have one_if_needed (bad:¬(L 1).map C≤L 1):(L 0).map C≤L 0:=by
    have lone:(orbitSites y d).card≤1:=by
      by_contra! h
      have dd:(orbitSites y d).card=2:=by change (orbitSites y d).card≤2 at few;omega
      have e:orbitBand y d 2=nodalOrbit y d:=by
        apply Submodule.eq_of_le_of_finrank_le (orbitBand_le _ _ _)
        rw [orbitBand_rank _ _ _ dd.ge,nodalOrbit_rank,dd]
      have e2:nodalOrbit y d=L 1:=by
        apply Submodule.eq_of_le_of_finrank_le
        · rw [←e];exact linear_orbit_le_primitiveBack 1
        · rw [nodalOrbit_rank,dd,ranks 1 (by decide)]
      apply bad
      rw [←e2]
      rintro _ ⟨w,hw,rfl⟩
      exact mulByBlock_mem y (nodalOrbit_mask y d) (fun a=>a) hw
    have dd:(orbitSites y d).card=1:=by
      by_contra h
      have nz' : ∃i,d i≠0:=by by_contra! no;exact nz (funext no)
      obtain ⟨i,hi⟩:=nz'
      have a:0<(orbitSites y d).card:=Finset.card_pos.mpr ⟨y i,Clock.headSites_mem _ hi⟩
      omega
    have e:orbitBand y d 1=nodalOrbit y d:=by
      apply Submodule.eq_of_le_of_finrank_le (orbitBand_le _ _ _)
      rw [orbitBand_rank _ _ _ dd.ge,nodalOrbit_rank,dd]
    have e1:nodalOrbit y d=L 0:=by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [←e];exact linear_orbit_le_primitiveBack 0
      · rw [nodalOrbit_rank,dd,ranks 0 (by decide)]
    rw [←e1]
    rintro _ ⟨w,hw,rfl⟩
    exact mulByBlock_mem y (nodalOrbit_mask y d) (fun a=>a) hw
  have ui:U.map C≤U:=by
    by_cases e:(L 1).map C≤L 1
    · simp [U,r,e]
    · simpa [U,r,e] using one_if_needed e
  have RR:1≤r ∧ r≤2:=by rcases rs with e|e <;> omega
  have rd:finrank K U=r:=by rw [show U=L (r-1) from rfl,ranks _ (by omega)];omega
  have IE(n:ℕ)(lo:r≤n)(up:n≤7):¬(L n).map C≤L n:=by
    by_cases hi:2≤n
    · exact esc n hi up
    have nn:n=1:=by omega
    have r1:r=1:=by omega
    have s:¬(L 1).map C≤L 1:=by
      intro e
      have rr:r=2:=ite_eq_left e
      omega
    simpa only [nn] using s
  have small:U≤L r:=mono (by omega)
  have ex:¬L r≤U:=by
    intro h
    have d:=Submodule.finrank_mono h
    rw [ranks _ (by omega),rd] at d
    omega
  obtain ⟨v,hv,vn⟩:=Set.not_subset.mp ex
  have hg:v∈U⊔annih U:=by rw [dot_split_own_annih];exact Submodule.mem_top
  obtain ⟨u,hu,τ,ht,h⟩:=Submodule.mem_sup.mp hg
  have tr:τ∈L r:=by
    have e:τ=v-u:=by rw [←h];abel
    rw [e]
    exact (L r).sub_mem hv (small hu)
  have tn:τ∉U:=fun e=>vn (h ▸ U.add_mem hu e)
  have e0:L r=chain C U τ 1:=by
    change L r=U⊔K∙τ
    apply (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · exact sup_le small ((Submodule.span_singleton_le_iff_mem ..).mpr tr)
    · rw [ranks _ (by omega),Submodule.finrank_sup_span_singleton tn,rd]
  have eq(n:ℕ)(hn:n<7)(lr:r≤n):L (n+1)=L n⊔(L n).map C:=by
    symm
    apply Submodule.eq_of_le_of_finrank_le (sup_le (mono (by omega)) (primitiveBack_clock _))
    have g: L n<L n⊔(L n).map C:=
      lt_of_le_of_ne le_sup_left (fun z=>IE n lr (by omega) (le_sup_right.trans z.ge))
    have h:=Submodule.finrank_lt_finrank_of_lt g
    rw [ranks _ (by omega)] at h
    change finrank K (L (n+1))≤finrank K ↥(L n⊔(L n).map C)
    rw [ranks _ (by omega)]
    omega
  have fl(k:ℕ)(h:r+k≤7):L (r+k)=chain C U τ (1+k):=by
    induction k with
    | zero=>simpa only [Nat.add_zero] using e0
    | succ n ih=>
      rw [show r+(n+1)=r+n+1 by omega,eq _ (by omega) (by omega),ih (by omega),
        chain_sup_map ui (by omega),Nat.add_assoc]
  have fl'(n:ℕ)(nl:r≤n)(nh:n≤7):L n=chain C U τ (n+1-r):=by
    have h:=fl (n-r) (by omega)
    rwa [show r+(n-r)=n by omega,show 1+(n-r)=n+1-r by omega] at h
  have E:annih (treeSpace A 8)=L 7:=(S.nonzeroCover nz).symm.trans (S.flags 7 (by decide)).2
  have ff:L 7=chain C U τ (8-r):=fl' 7 (by omega) (by decide)
  have high: (8-r)<(headSites y τ).card:=by
    apply more_sites_than_paid (c:=y) (F:=L 7)
    · intro n hn
      rw [ff]
      exact ((chain_le_iff _).mp le_rfl).2 n hn
    · intro hc
      apply IE 7 (by omega) (by decide)
      have eq:chain C U τ (8-r+1)=L 7:=by
        apply Submodule.eq_of_le_of_finrank_le ?_ ?_
        · apply (chain_le_iff _).mpr
          refine ⟨mono (by omega),?_⟩
          intro j hj
          by_cases top:j=8-r
          · rwa [top]
          · rw [ff]
            exact ((chain_le_iff _).mp le_rfl).2 j (by omega)
        · rw [←chain_sup_map ui (by omega),←ff]
          exact Submodule.finrank_mono le_sup_left
      have m:(L 7).map C≤chain C U τ (8-r+1):=by
        rw [←chain_sup_map ui (show 0<8-r by omega),←ff]
        exact le_sup_right
      exact m.trans eq.le
  have big:9-r≤(headSites (mirror A) τ).card:=by
    change 9-r≤(headSites y τ).card
    omega
  refine ⟨r,U,τ,⟨rs,rfl,rd,ui,ht,?_,big,fl',E.trans ff⟩⟩
  apply primitiveBack_annih ho _ r (by omega)
  exact tr

end
end RKCert.Paired.ReverseHull

