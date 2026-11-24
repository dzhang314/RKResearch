module

public import RKCert.ERKOrderNineGoodPrimeLift

@[expose] public section

/-! # Small-factor modular coverage

A checked factor of the parameter equation has four checked root slots.
Successive synthetic relations select different *slots*, without a
squarefreeness or distinctness assumption after prime reduction.  Each
terminal test is a unit witness in the small parameter coefficient
quotient. -/
namespace RKCert.GoodPrimeDense
open Polynomial

noncomputable def Three.polynomial {R : Type*} [CommRing R] (q : Three R) : R[X] :=
  ofCoeffList [q.a,q.b,q.c,1]

noncomputable def Two.polynomial {R : Type*} [CommRing R] (q : Two R) : R[X] :=
  ofCoeffList [q.a,q.b,1]

theorem Three.polynomial_eval {R : Type*} [CommRing R] (q : Three R) (x : R) :
    q.polynomial.eval x = q.eval x := by
  simp [Three.polynomial,Three.eval,ofCoeffList_cons]
  ring

theorem Two.polynomial_eval {R : Type*} [CommRing R] (q : Two R) (x : R) :
    q.polynomial.eval x = q.eval x := by
  simp [Two.polynomial,Two.eval,ofCoeffList_cons]
  ring

theorem Four.polynomial_factor {K : Type*} [Field K] {q : Four K} {h : K}
    (hh : q.eval h=0) :
    q.polynomial = (X-C h)*(q.shifted h).polynomial := by
  -- Linear-root division, valid over finite as well as infinite fields.
  simp only [Four.eval] at hh
  have eq : q.a=-(h^4+q.d*h^3+q.c*h^2+q.b*h) := by linear_combination hh
  simp [Four.polynomial,Three.polynomial,ofCoeffList_cons,Four.shifted,eq]
  ring

theorem Three.polynomial_factor {K : Type*} [Field K] {q : Three K} {u : K}
    (uu : q.eval u=0) :
    q.polynomial = (X-C u)*(q.shifted u).polynomial := by
  have eq : q.a=-(u^3+q.c*u^2+q.b*u) := by
    unfold Three.eval at uu
    linear_combination uu
  simp [Three.polynomial,Two.polynomial,ofCoeffList_cons,Three.shifted,eq]
  ring

theorem slots_of_rootSystem {K : Type*} [Field K] {q : Four K} {h u v : K}
    (T : Fin 4→K) (split : q.polynomial = ∏i, (X-C (T i)))
    (roots : RootSystem q h u v) :
    ∃ a b c : Fin 4, a≠b ∧ a≠c ∧ b≠c ∧ h=T a ∧ u=T b ∧ v=T c := by
  classical
  let f : Fin 4→K[X] := fun i => X-C (T i)
  have find (S : Finset (Fin 4)) (x : K) (hx : (∏i∈S, f i).eval x=0) :
      ∃ i∈S, x=T i := by
    rw [Polynomial.eval_prod] at hx
    obtain ⟨i,hi,hx⟩ := Finset.prod_eq_zero_iff.mp hx
    exact ⟨i,hi,sub_eq_zero.mp (by simpa [f] using hx)⟩
  have zh : (∏ i, f i).eval h=0 := by
    rw [←split,Four.polynomial_eval]
    exact roots.four
  obtain ⟨a,ha,eh⟩ := find Finset.univ h zh
  have ch : (q.shifted h).polynomial = ∏ i ∈ Finset.univ.erase a,f i := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero h)
    rw [←Four.polynomial_factor roots.four,split,eh]
    exact (Finset.mul_prod_erase _ f ha).symm
  have zu : (∏ i ∈ Finset.univ.erase a, f i).eval u=0 := by
    rw [←ch,Three.polynomial_eval]
    exact roots.three
  obtain ⟨b,hb,eu⟩ := find (Finset.univ.erase a) u zu
  have cu : ((q.shifted h).shifted u).polynomial =
      ∏ i ∈ (Finset.univ.erase a).erase b,f i := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero u)
    rw [←Three.polynomial_factor roots.three,ch,eu]
    exact (Finset.mul_prod_erase _ f hb).symm
  have zv : (∏ i ∈ (Finset.univ.erase a).erase b, f i).eval v=0 := by
    rw [←cu,Two.polynomial_eval]
    exact roots.two
  obtain ⟨c,hc,ev⟩ := find ((Finset.univ.erase a).erase b) v zv
  exact ⟨a,b,c,(Finset.ne_of_mem_erase hb).symm,
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)).symm,
    (Finset.ne_of_mem_erase hc).symm,eh,eu,ev⟩

def linearRecipe {A : Type*} (o : Operations A) (z : A) : List A :=
  [o.neg z,o.int 1]

def splitRecipe {A : Type*} (o : Operations A) (T : Fin 4→A) : List A :=
  times o (linearRecipe o (T 0)) (times o (linearRecipe o (T 1))
    (times o (linearRecipe o (T 2)) (linearRecipe o (T 3))))

def pencilPolynomialRecipe {A : Type*} (o : Operations A) (l d : A) : List A :=
  let q := pencilRecipe o l d
  [q.a,q.b,q.c,q.d,o.int 1]

theorem decode_linearRecipe {A R : Type*} [CommRing R]
    {o : Operations A} {f : A→R} (s : Sound o f) (z : A) :
    decode f (linearRecipe o z) = X-C (f z) := by
  simp [decode,linearRecipe,s.neg,s.int,ofCoeffList_cons,map_neg,sub_eq_add_neg,add_comm]

theorem decode_splitRecipe {A R : Type*} [CommRing R]
    {o : Operations A} {f : A→R} (s : Sound o f) (T : Fin 4→A) :
    decode f (splitRecipe o T) = ∏ i : Fin 4, (X-C (f (T i))) := by
  simp [splitRecipe,decode_times s,decode_linearRecipe s,Fin.prod_univ_succ]

theorem decode_pencilPolynomialRecipe {A R : Type*} [CommRing R]
    {o : Operations A} {f : A→R} (s : Sound o f) (l d : A) :
    decode f (pencilPolynomialRecipe o l d) = (pencilAt (f l) (f d)).polynomial := by
  simp only [decode,pencilPolynomialRecipe,List.map_cons,List.map_nil,s.int,Int.cast_one]
  rw [←map_pencilRecipe s l d]
  rfl

structure SplitDatum (p : ℕ) where
  rel : List (ZMod p)
  knots : Fin 4 → List (ZMod p)
  inv : Fin 4 → Fin 4 → Fin 4 → List (ZMod p)

variable {p : ℕ}

def SplitDatum.ops (S : SplitDatum p) : Operations (List (ZMod p)) :=
  quotient (scalar (ZMod p)) S.rel

noncomputable def SplitDatum.factor (S : SplitDatum p) : (ZMod p)[X] :=
  X^S.rel.length - ofCoeffList S.rel

def SplitDatum.splitCheck (S : SplitDatum p) (d : ZMod p) : Prop :=
  pencilPolynomialRecipe S.ops (generator (scalar _)) (constant (scalar _) d) =
    splitRecipe S.ops S.knots

def SplitDatum.unitCheck (S : SplitDatum p) (d : ZMod p) (a b c : Fin 4) : Prop :=
  S.ops.mul (terminalRecipe S.ops (S.knots a) (S.knots b) (S.knots c)
    (generator (scalar _)) (constant (scalar _) d)) (S.inv a b c) = [1]

theorem SplitDatum.terminal_nonzero {E : Type*} [Field E]
    (S : SplitDatum p) (ψ : ZMod p→+*E)
    (d : ZMod p) (h u v l : E) (sz : 0 < S.rel.length)
    (verifySplit : S.splitCheck d)
    (verifyUnit : ∀ a b c, a≠b → a≠c → b≠c → S.unitCheck d a b c)
    (froot : (S.factor.map ψ).eval l=0)
    (root : RootSystem (pencilAt l (ψ d)) h u v) :
    terminalAt h u v l (ψ d) ≠ 0 := by
  have bf := Sound.scalar ψ
  let f : List (ZMod p)→E := read ψ l
  have rr : read ψ l S.rel = l^S.rel.length := by
    unfold SplitDatum.factor at froot
    rw [Polynomial.map_sub,Polynomial.map_pow,map_X,eval_sub,eval_pow,eval_X,
      ←eval₂_eq_eval_map,eval₂_ofCoeffList_read,sub_eq_zero] at froot
    exact froot.symm
  have s : Sound S.ops f := Sound.quotient bf l sz rr
  have aL : f (generator (scalar _)) = l := read_generator bf l
  have dV : f (constant (scalar _) d) = ψ d := read_constant bf l d
  have hsplit := congrArg (decode f) verifySplit
  rw [decode_pencilPolynomialRecipe s,decode_splitRecipe s,aL,dV] at hsplit
  obtain ⟨a,b,c,ab,ac,bc,rfl,rfl,rfl⟩ := slots_of_rootSystem (fun i=>f (S.knots i)) hsplit root
  intro z
  have eq := congrArg f (verifyUnit a b c ab ac bc)
  rw [s.mul,eval_terminalRecipe s,aL,dV,z,zero_mul] at eq
  have E1 : f [1] = 1 := by simp [f,read]
  exact zero_ne_one (eq.trans E1)

end RKCert.GoodPrimeDense
