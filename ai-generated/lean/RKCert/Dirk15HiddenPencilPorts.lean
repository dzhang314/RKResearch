module

public import RKCert.Dirk15HiddenSignatureArrays
public import RKCert.EndpointJacobiPencilSix
public import RKCert.Dirk15NativePivots
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

/-! # A hidden actual head gives a small factor and a true clean pivot

The arithmetic callback still needed to contradict the pivot lies in a
separate fixed/free pencil resultant. No property of a deleted weighted
tableau, and no positivity on the coefficient field, is used.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace Order15HiddenHead
variable {h : Order15HiddenHead A b} {D : h.head.DeletedPencil}

set_option maxHeartbeats 1700000 in
theorem NativeSquareSignatures.factor [IsAlgClosed K] (S : h.NativeSquareSignatures D)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b) :
    D.D=S.R*S.T ∧ S.T≠0 ∧
      ∀ i : Fin 20,i≠Fin.last 19→i∉ghostPositions A b→h.head.w i≠0→
        h.head.w i=S.T.eval (nodes A i) := by
  have dN : D.D≠0 := by
    intro z
    have b := D.dmin
    rw [z,natDegree_zero] at b
    omega
  have ident := Order15HiddenHead.NativeSquareSignatures.exact_identity h D S ha ho H
  unfold Signature.squareSignatureExpression at ident
  have eq : D.D*(D.D-S.R*S.T)=C S.scale*S.V*S.R^2 := by linear_combination ident
  have rN : S.R≠0 := by
    intro z
    rw [z,zero_mul,sub_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero] at eq
    exact dN ((mul_eq_zero.mp eq).elim id id)
  have elim {G L : K[X]} (a : K) (an : a≠0) (dg : D.D=C a*(X*G)) (vl : S.V=X*L)
      (roots : 6≤G.roots.toFinset.card) (cop : IsCoprime G L) : S.scale=0 := by
    by_contra nz
    have e : C a*(D.D-S.R*S.T)*G=C S.scale*L*S.R^2 := by
      apply mul_left_cancel₀ X_ne_zero
      calc
        _=(C a*(X*G))*(D.D-S.R*S.T) := by ring
        _=D.D*(D.D-S.R*S.T) := by rw [←dg]
        _=C S.scale*S.V*S.R^2 := eq
        _=_ := by rw [vl]; ring
    have dd : G∣C S.scale*(L*S.R^2) := ⟨C a*(D.D-S.R*S.T),by rw [mul_comm G]; simpa only [mul_assoc] using e.symm⟩
    obtain ⟨q,eq_q⟩ := dd
    have cancel : C S.scale⁻¹*C S.scale=1 := by rw [←map_mul,inv_mul_cancel₀ nz,map_one]
    have d : G∣L*S.R^2 := by
      refine ⟨C S.scale⁻¹*q,?_⟩
      calc
        _ = C S.scale⁻¹*(C S.scale*(L*S.R^2)) := by rw [←mul_assoc,cancel,one_mul]
        _ = C S.scale⁻¹*(G*q) := by rw [eq_q]
        _ = _ := by ring
    have dl : G∣S.R^2 := cop.dvd_of_dvd_mul_left d
    have rsub : G.roots.toFinset⊆S.R.roots.toFinset := by
      intro z zm
      have g := isRoot_of_mem_roots (Multiset.mem_toFinset.mp zm)
      have r := g.dvd dl
      have y : S.R.eval z=0 := by
        change (S.R^2).eval z=0 at r
        rw [eval_pow] at r
        exact sq_eq_zero_iff.mp r
      exact Multiset.mem_toFinset.mpr ((mem_roots rN).mpr y)
    have s := Finset.card_le_card rsub
    have h := (Multiset.toFinset_card_le S.R.roots).trans ((card_roots' _).trans S.Rdegree)
    omega
  have z : S.scale=0 := by
    rcases S.branch with ⟨v,a,an,dg⟩|⟨v,a,t,an,dg⟩
    · have ns := jacobiTwo_fixed_simple (K:=K) 6 (by decide)
      have roots : 6≤(jacobiTwo K 6).roots.toFinset.card := by
        rw [Multiset.toFinset_card_of_nodup ns,←(IsAlgClosed.splits _).natDegree_eq_card_roots,
          jacobiTwo_degree]
      exact elim a an dg v roots (jacobiTwo_adjacent_coprime (K:=K) 6).symm
    · have co : IsCoprime (jacobiTwo K 7+C t*jacobiTwo K 6) (jacobiTwo K 6) := by
        obtain ⟨p,q,eq⟩ := jacobiTwo_adjacent_coprime (K:=K) 6
        exact ⟨p,q-p*C t,by linear_combination eq⟩
      exact elim a an dg v (jacobiTwo_seven_pencil_distinct t) co
  have e : D.D=S.R*S.T := by
    rw [z,map_zero,zero_mul,zero_mul] at eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left dN)
  refine ⟨e,fun t => dN (by rw [e,t,mul_zero]),fun i it ig iw => ?_⟩
  have base := S.square i it ig
  rw [z,zero_mul,add_zero,pow_two] at base
  exact mul_left_cancel₀ iw base

set_option maxHeartbeats 1700000 in
theorem NativeSquareSignatures.true_forward_pivot [IsAlgClosed K] (S : h.NativeSquareSignatures D)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b) :
    ∃ u : K, u≠0 ∧ D.D.eval u=0 ∧ S.T∣D.D ∧ S.T.eval u≠0 ∧
      paidMoment S.T u 1=0 ∧ paidMoment S.T u 2=0 := by
  classical
  obtain ⟨factor,pn,matchHead⟩ := S.factor ha ho H
  let c := nodes A
  let C' := diag c
  let w := h.head.w
  let P := S.T
  let g : Vec K 20 := fun i => if i∈ghostPositions A b then P.eval (c i) else 0
  let η := evalNodes A P-g-w
  let θ := C' η
  let F := zeroSpace A
  have gu : g∈h.head.U := by
    rw [h.core_eq]
    apply simultaneousGhosts_mem.mpr
    refine ⟨by simp [g,mem_ghostPositions],fun i hi => ?_⟩
    have nm : i∉ghostPositions A b := fun e => hi.elim
      (fun h => h (mem_ghostPositions.mp e).2.1) (fun h => h (mem_ghostPositions.mp e).2.2)
    simp [g,nm]
  have U5 : h.head.U≤F 5 := by
    change h.head.U≤zeroSpace A 5
    rw [h.five]
    exact ((chain_le_iff _).mp le_rfl).1
  have cgu : C' g∈h.head.U := h.head.maximal.2.1 (Submodule.mem_map_of_mem gu)
  have arr := ((chain_le_iff (T:=C') (U:=h.head.U) (w:=w) 2).mp le_rfl).2
  have hw : w∈F 5 := h.five.ge (by simpa only [pow_zero,one_apply_eq_self] using arr 0 (by decide))
  have cw : C' w∈F 5 := h.five.ge (by simpa only [pow_one] using arr 1 (by decide))
  have base : OrdinaryTrace A 5 η P :=
    ((OrdinaryTrace.scalar A (S.Tdegree.trans (by decide))).sub_pure (U5 gu)).sub_pure hw
  have E : θ=evalNodes A (X*P)-C' g-C' w := by
    change C' (evalNodes A P-g-w)=_
    rw [map_sub,map_sub]
    have x := evaluateColumn_clock (A:=A) P
    simpa only [evaluateColumn_eq] using congrArg (fun v : Vec K 20 => v-C' g-C' w) x
  have th : OrdinaryTrace A 5 θ (X*P) := by
    rw [E]
    have d : (X*P).natDegree≤5 :=
      natDegree_mul_le.trans (by rw [natDegree_X]; have t : P.natDegree≤4 := S.Tdegree; omega)
    exact ((OrdinaryTrace.scalar A d).sub_pure (U5 cgu)).sub_pure cw
  obtain ⟨l,lt,ln⟩ := OrdinaryTrace.nonterminal_clock_witness pn S.Tdegree base ho
    (by decide) (Fin.last 19) H.terminal.node_one
  have nonzero : θ≠0 := fun e => ln (by change θ l=0; rw [e,Pi.zero_apply])
  obtain ⟨i,iz,before⟩ := exists_first_coordinate nonzero
  have it : i≠Fin.last 19 := by
    intro eq
    have e : l < i := by rw [eq]; exact lt_of_le_of_ne (Fin.le_last l) lt
    exact ln (before l e)
  have coord : θ i=c i*(P.eval (c i)-g i-w i) := by
    simp only [θ,C',diag_apply,η,Pi.sub_apply,evalNodes_apply,c]
  have ig : i∉ghostPositions A b := by
    intro e
    apply iz
    have gP : g i=P.eval (c i) := by simp [g,e]
    have w0 : w i=0 := h.head_zero i e
    rw [coord,gP,w0,sub_self,sub_zero,mul_zero]
  have g0 : g i=0 := by simp [g,ig]
  have iw : w i=0 := by
    by_contra e
    apply iz
    have p : w i=P.eval (c i) := matchHead i it ig e
    rw [coord,g0,p,sub_zero,sub_self,mul_zero]
  have iv : θ i=c i*P.eval (c i) := by rw [coord,g0,iw,sub_zero,sub_zero]
  have root := S.relation i it ig
  rw [show h.head.w i=0 from iw,zero_mul] at root
  have clean : ∀ v∈F 7,v i=0 := by
    intro v vp
    obtain ⟨Q,_,he⟩ := h.read_tail (h.head.seven.le vp)
    simpa only [show h.head.w i=0 from iw,mul_zero] using he i ig
  have moments := OrdinaryTrace.two_primitive_first_pivot ha ho th (by decide : 5+2≤7)
    (by decide) iz before clean
  exact ⟨c i,(fun e => iz (by rw [iv,e,zero_mul])),root,
    ⟨S.R,by rw [factor,mul_comm]⟩,fun e => iz (by rw [iv,e,mul_zero]),moments.2⟩

end Order15HiddenHead
end
end RKCert.Paired
