module
public import RKCert.ERKOddBalancedRanks

@[expose] public section
/-! # Genuine odd-order reverse-hull branches
Only the true terminal-zero annihilator is used when the first adjoint
seed vanishes. In the nonzero case the whole annihilator is thin; the
route to it need not be a one-seed orbit. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Endpoint RKCert.Paired.FiniteMidpoint
open Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem balanced_odd_reverse_gap (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+1))
    (h8:8≤q)(size:s+1=3*q+2)(S:OddBalanced A b q)
    (n:ℕ)(nl:2≤n)(nh:n≤q-1) :
    ¬(primitiveBack A b n).map (diag (mirror A))≤primitiveBack A b n := by
  intro inv
  have rank (k:ℕ) (hk:k≤q-1) : finrank K (primitiveBack A b k)=k+finrank K (back A b 0) := by
    rw [←(S.flags _ hk).2,(S.flags _ hk).1]
  have gain:=primitiveBack_invariant_gain ha ho n (by omega) inv
  rw [rank n nh] at gain
  by_cases e:n=q-1
  · rw [e,show q-1+1=q by omega] at gain
    by_cases z:backSeed1 A b=0
    · have out:terminal (K:=K) s∉treeSpace A (q-1):=
        fun t=>S.terminalOut z (treeSpace_mono A (by omega) t)
      have last (v:Vec K (s+1))(hv:v∈primitiveBack A b q):row v (terminal s)=0:=by
        rw [row_terminal]
        exact primitiveBack_terminal _ (S.lastReflect z) (fun i=>ha i _ (Fin.le_last i)) z _ hv
      have bill:=annihilating_terminal_count (terminal s) out (primitiveBack_annih ho (q-1) q (by omega)) last
      change finrank K (treeSpace A (q-1))+finrank K (primitiveBack A b q)+1≤s+1 at bill
      have low:=S.treePrev
      omega
    · have base:finrank K (back A b 0)=1:=finrank_span_singleton z
      have bill:=finrank_annih_le (primitiveBack_annih ho (q-1) q (by omega))
      have low:=S.treePrev
      omega
  · rw [rank (n+1) (by omega)] at gain
    omega

noncomputable section
/-- Zero-linear-seed branch has exactly the true second-seed orbit through
the last original terminal-zero marked horizon. -/
structure OddZeroReverse (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q:ℕ) : Prop where
  firstZero : backSeed1 A b=0
  lastNode : nodes A (Fin.last s)=1
  lastSeed : backSeed2 A b (Fin.last s)=0
  sites : q≤(orbitSites (mirror A) (backSeed2 A b)).card
  orbit : annih (treeSpace A q)⊓LinearMap.ker (LinearMap.proj (Fin.last s))=
    orbitBand (mirror A) (backSeed2 A b) (q-1)

set_option maxHeartbeats 2100000 in
theorem balanced_odd_zero_reverse (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b (2*q+1))
    (h8:8≤q)(size:s+1=3*q+2)(S:OddBalanced A b q)(z:backSeed1 A b=0):OddZeroReverse A b q:=by
  classical
  let H:=q-1
  let d:=backSeed2 A b
  let y:=mirror A
  let L:=primitiveBack A b
  have zr:finrank K (back A b 0)=0:=by
    change finrank K (K∙backSeed1 A b)=0
    rw [z,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]
  have f(n:ℕ)(hn:n≤H):finrank K (back A b n)=n ∧ back A b n=L n:=by
    obtain ⟨r,e⟩:=S.flags n hn
    exact ⟨by rw [r,zr,add_zero],e⟩
  have ranks(n:ℕ)(hn:n≤H):finrank K (L n)=n:=by rw [←(f n hn).2,(f n hn).1]
  have escapes(n:ℕ)(hn:2≤n)(hi:n≤H):¬(L n).map (diag y)≤L n:=
    balanced_odd_reverse_gap ha ho h8 size S n hn hi
  have loc:UnitFirstFour A b:=by
    refine ⟨z,fun n hn=>(f n (by dsimp [H];omega)).1,?_,?_,?_,?_⟩
    · rw [(f 2 (by dsimp [H];omega)).2]
      exact escapes 2 (by decide) (by dsimp [H];omega)
    · rw [(f 3 (by dsimp [H];omega)).2]
      exact escapes 3 (by decide) (by dsimp [H];omega)
    · rw [(f 2 (by dsimp [H];omega)).2,residual_eq_reflectedError]
      exact reflectedError_mem_primitiveBack (X^2) 1 (by simp)
    · rw [(f 3 (by dsimp [H];omega)).2,residual_eq_reflectedError]
      exact reflectedError_mem_primitiveBack (X^3) 2 (by simp)
  have pos:(orbitSites y d).card≠0:=by
    intro ct
    have dz:d=0:=by
      ext i;by_contra dn
      exact (Finset.card_ne_zero.mpr ⟨_,Clock.headSites_mem (c:=y) i dn⟩) ct
    have B0:back A b 0=⊥:=Submodule.finrank_eq_zero.mp zr
    have B1:back A b 1=⊥:=by
      change back A b 0⊔(back A b 0).map (transMat A)⊔(back A b 0).map (diag y)⊔(K∙d)=⊥
      simp [B0,dz]
    have R:=loc.rank 1 (by decide)
    have Z:=Submodule.finrank_eq_zero.mpr B1
    omega
  have enough:q≤(orbitSites y d).card:=by
    by_contra! small
    let n:ℕ:=(orbitSites y d).card
    have hi:n≤H:=by dsimp only [n,H];omega
    have no1:n≠1:=unit_no_single_reverse_site ha ho (by omega) loc
    have lo:2≤n:=by have nn:n≠0:=pos;omega
    have all:orbitBand y d n=nodalOrbit y d:=by
      apply Submodule.eq_of_le_of_finrank_le (orbitBand_le y d n)
      rw [orbitBand_rank y d n le_rfl,nodalOrbit_rank]
    have full:nodalOrbit y d=L n:=by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [←all];exact orbitBand_le_primitiveBack _
      · rw [nodalOrbit_rank,ranks n hi]
    apply escapes n lo hi
    rw [←full]
    rintro _ ⟨w,hw,rfl⟩
    exact mulByBlock_mem y (nodalOrbit_mask y d) (fun a=>a) hw
  have band:orbitBand y d H=L H:=by
    apply Submodule.eq_of_le_of_finrank_le (orbitBand_le_primitiveBack H)
    rw [ranks H le_rfl,orbitBand_rank y d H (by dsimp [H];omega)]
  have dlast:d (Fin.last s)=0:=primitiveBack_terminal _ (S.lastReflect z)
    (fun i=>ha _ _ (Fin.le_last i)) z 1 (seed2_mem_primitiveBack 0)
  exact ⟨z,(sub_eq_zero.mp (S.lastReflect z)).symm,dlast,enough,
    (S.zeroCover z).symm.trans ((f H le_rfl).2.trans band.symm)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem OddZeroReverse.poly_cover (S:OddZeroReverse A b q)(q2:2≤q)
    {u:Vec K (s+1)} (hu:u∈annih (treeSpace A q)⊓LinearMap.ker (LinearMap.proj (Fin.last s))) :
    ∃P:K[X],P.natDegree≤q-2 ∧ weightedEval (mirror A) (backSeed2 A b) P=u:=by
  let : DecidableEq K:=Classical.decEq K
  rw [S.orbit] at hu
  obtain ⟨a,eq⟩:=hu
  let P:K[X]:=ofFn (q-1) a
  refine ⟨P,by have e:=ofFn_natDegree_lt (by omega:0<q-1) a;change P.natDegree<q-1 at e;omega,?_⟩
  rwa [LinearMap.comp_apply] at eq

/-- The linear adjoint seed pays its own stage: q successive independent
clock powers begin at reverse index zero. -/
theorem linear_orbit_le_primitiveBack (n:ℕ) :
    orbitBand (mirror A) (backSeed1 A b) (n+1)≤primitiveBack A b n:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let d:=backSeed1 A b
  let y:=mirror A
  have mono:Monotone (primitiveBack A b) := monotone_nat_of_le_succ primitiveBack_le_succ
  have pw(k:ℕ):(diag y^k) d∈primitiveBack A b k:=by
    induction k with
    | zero =>
      simp only [pow_zero,one_apply_eq_self]
      exact back_le_primitiveBack 0 (Submodule.mem_span_singleton_self d)
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp]
      exact primitiveBack_clock k (Submodule.mem_map_of_mem ih)
  rintro _ ⟨a,rfl⟩
  let P:=ofFn (n+1) a
  let E:=weightedEval y d
  rw [LinearMap.comp_apply]
  change E P∈primitiveBack A b n
  rw [P.as_sum_range' _ (ofFn_natDegree_lt (by omega) a),map_sum]
  apply (primitiveBack A b n).sum_mem
  intro k hk
  have eq:E (monomial k (P.coeff k))=P.coeff k • (diag y^k) d:=by
    ext i;simp [E,eval_monomial,pow_diag_apply,smul_eq_mul,mul_assoc]
  rw [eq]
  exact (primitiveBack A b n).smul_mem _ (mono (by have:=Finset.mem_range.mp hk;omega) (pw k))

theorem balanced_odd_broad_or_local (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b (2*q+1))
    (h8:8≤q)(size:s+1=3*q+2)(S:OddBalanced A b q)(z:backSeed1 A b≠0) :
    let n:=(orbitSites (mirror A) (backSeed1 A b)).card
    n≤2 ∨ (q+1≤n ∧ annih (treeSpace A q)=orbitBand (mirror A) (backSeed1 A b) q):=by
  classical
  let y:=mirror A
  let d:=backSeed1 A b
  let n:=(orbitSites y d).card
  let L:=primitiveBack A b
  have base:finrank K (back A b 0)=1:=finrank_span_singleton z
  have r(k:ℕ)(hk:k≤q-1):finrank K (L k)=k+1:=by
    change finrank K (primitiveBack A b k)=_
    rw [←(S.flags _ hk).2,(S.flags _ hk).1,base]
  change n≤2 ∨ (q+1≤n ∧ annih (treeSpace A q)=orbitBand y d q)
  by_cases tiny:n≤2
  · exact Or.inl tiny
  right
  have big:q+1≤n:=by
    by_contra! small
    let k:=n-1
    have scarce:k+1=n:=by dsimp [k];omega
    have kq:k≤q-1:=by dsimp [k];omega
    have full:orbitBand y d (k+1)=nodalOrbit y d:=by
      apply Submodule.eq_of_le_of_finrank_le (orbitBand_le _ _ _)
      rw [orbitBand_rank _ _ _ (by rw [scarce]),nodalOrbit_rank,scarce]
    have eq:nodalOrbit y d=L k:=by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [←full];exact linear_orbit_le_primitiveBack k
      · rw [nodalOrbit_rank,r k kq];exact scarce.le
    apply balanced_odd_reverse_gap ha ho h8 size S k (by dsimp [k];omega) kq
    rw [show primitiveBack A b k=L k from rfl,←eq]
    rintro _ ⟨w,hw,rfl⟩
    exact mulByBlock_mem y (nodalOrbit_mask y d) (fun a=>a) hw
  refine ⟨big,?_⟩
  rw [←S.nonzeroCover z,(S.flags _ le_rfl).2]
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le
  · rw [show q=(q-1)+1 by omega]
    exact linear_orbit_le_primitiveBack (q-1)
  · rw [show primitiveBack A b (q-1)=L (q-1) from rfl,r _ le_rfl,
      orbitBand_rank y d q (by omega)]
    omega
end
end RKCert.Paired.ReverseHull
