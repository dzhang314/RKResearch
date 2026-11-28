module
public import RKCert.ReviewedNative.ERK10FixedQ29AdicZTailSound
@[expose] public section

namespace RKResearch.Certified.ERK10ZTailCore
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type u} [Lean.Grind.CommRing R]
set_option maxRecDepth 16000
set_option maxHeartbeats 500000

def Invertible (a : R) : Prop := ∃ w, w*a=1

theorem inver_one (R : Type u) [Lean.Grind.CommRing R] :
    Invertible (1:R) := ⟨1, by grind⟩

theorem inver_mul {a b : R} (ha : Invertible a) (hb : Invertible b) :
    Invertible (a*b) := by
  obtain ⟨w,hw⟩ := ha
  obtain ⟨v,hv⟩ := hb
  refine ⟨w*v,?_⟩
  calc
    _ = (w*a)*(v*b) := by grind
    _ = _ := by rw [hw,hv];grind

theorem inver_pow {a : R} (ha : Invertible a) (n : Nat) :
    Invertible (a^n) := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact inver_one R
  | succ n ih => rw [Semiring.pow_succ]; exact inver_mul ih ha

/-- Carry the interpretation and its own paid denominator together. -/
def Reads (x0 : R) (a : Rep) (x : R) : Prop :=
  Represents x0 a x ∧ Invertible (a.den:R)

theorem reads_zero (x0 : R) {a : Rep} {x : R}
    (h : Reads x0 a x) (hz : zero a=true) : x=0 := by
  obtain ⟨hR,⟨w,hw⟩⟩ := h
  exact check_sound x0 hR hz hw

theorem reads_int (x0 : R) (i : Int) : Reads x0 (con i) (i:R) := by
  refine ⟨?_,?_⟩
  · change (i:R)+x0*0=((1:Nat):R)*(i:R)
    rw [Semiring.natCast_one]
    grind
  · change Invertible ((1:Nat):R)
    rw [Semiring.natCast_one]
    exact inver_one R

theorem reads_nat (x0 : R) (i : Nat) :
    Reads x0 (OfNat.ofNat (α:=Rep) i) (OfNat.ofNat (α:=R) i) := by
  change Reads x0 (con (Int.ofNat i)) _
  rw [Semiring.ofNat_eq_natCast,←int_ofNat_cast]
  exact reads_int x0 _

theorem reads_c (x0 : R) : Reads x0 RKResearch.Certified.ERK10ZTailCore.c x0 := by
  change Reads x0 ⟨[0,1],1⟩ x0
  refine ⟨?_,?_⟩
  · change ((0:Int):R)+x0*(((1:Int):R)+x0*0)=((1:Nat):R)*x0
    rw [Ring.intCast_zero,Ring.intCast_one,Semiring.natCast_one]
    grind
  · change Invertible ((1:Nat):R)
    rw [Semiring.natCast_one]
    exact inver_one R

theorem reads_add (x0 : R) {a b : Rep} {x y : R}
    (ha : Reads x0 a x) (hb : Reads x0 b y) : Reads x0 (a+b) (x+y) := by
  refine ⟨represents_add x0 ha.1 hb.1,?_⟩
  change Invertible ((a.den*b.den:Nat):R)
  rw [Semiring.natCast_mul]
  exact inver_mul ha.2 hb.2

theorem reads_neg (x0 : R) {a : Rep} {x : R}
    (ha : Reads x0 a x) : Reads x0 (-a) (-x) :=
  ⟨represents_neg x0 ha.1,ha.2⟩

theorem reads_sub (x0 : R) {a b : Rep} {x y : R}
    (ha : Reads x0 a x) (hb : Reads x0 b y) : Reads x0 (a-b) (x-y) := by
  rw [Ring.sub_eq_add_neg]
  exact reads_add x0 ha (reads_neg x0 hb)

theorem reads_mul (x0 : R) (hroot : evalI x0 decic=0)
    (hL : Invertible (leading:R))
    {a b : Rep} {x y : R} (ha : Reads x0 a x) (hb : Reads x0 b y) :
    Reads x0 (a*b) (x*y) := by
  refine ⟨represents_mul x0 hroot ha.1 hb.1,?_⟩
  let xs:=conv a.nums b.nums
  change Invertible (((reduce (xs.length-10) xs (a.den*b.den)).den:Nat):R)
  rw [reduce_den,Semiring.natCast_mul,Semiring.natCast_mul,Semiring.natCast_pow]
  exact inver_mul (inver_mul ha.2 hb.2) (inver_pow hL _)

theorem reads_pow (x0 : R) (hroot : evalI x0 decic=0)
    (hL : Invertible (leading:R))
    {a : Rep} {x : R} (ha : Reads x0 a x) (n : Nat) :
    Reads x0 (a^n) (x^n) := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact reads_nat x0 1
  | succ n ih =>
    rw [Semiring.pow_succ]
    exact reads_mul x0 hroot hL ih ha

def inputSlots : List Rep :=
  [S,Q,E,F,sigma,v0,v1,v2,q0,q1,q2,q3,mu0,mu1,mu2,mu3,mu4,mu5,mu6]

theorem leading_mod_ne : leading%29 != 0 := by decide +kernel

theorem slot_mod_ne {p : Rep} (h : p∈inputSlots) : p.den%29 != 0 := by
  have hall : inputSlots.all paidDen = true := (Bool.and_eq_true_iff.mp den_paid).2
  exact List.all_eq_true.mp hall _ h

structure ReadContext (x0 : R) where
  root : evalI x0 decic=0
  leading_paid : Invertible (leading:R)
  inverse : Nat→R
  literal_paid : ∀ p ∈ inputSlots, inverse p.den*(p.den:R)=1

def ReadContext.value {x0 : R} (ctx : ReadContext x0) (p : Rep) : R :=
  ctx.inverse p.den * evalI x0 p.nums

theorem ReadContext.literal {x0 : R} (ctx : ReadContext x0)
    {p : Rep} (hp : p∈inputSlots) : Reads x0 p (ctx.value p) := by
  have h := ctx.literal_paid p hp
  refine ⟨?_,⟨_,h⟩⟩
  unfold Represents ReadContext.value
  calc
    _ = (ctx.inverse p.den*(p.den:R))*evalI x0 p.nums := by rw [h];grind
    _ = _ := by grind

def evalReal (ps : List R) (y : R) : R := ps.foldr (fun a z => a+y*z) 0

theorem reads_eval {x0 : R} (ctx : ReadContext x0)
    (ps : List Rep) {x : Rep} {y : R} (hy : Reads x0 x y)
    (hs : ∀ p∈ps, p∈inputSlots) :
    Reads x0 (eval ps x) (evalReal (ps.map ctx.value) y) := by
  induction ps with
  | nil => exact reads_nat x0 0
  | cons p ps ih =>
    change Reads x0 (p+x*eval ps x) (ctx.value p+y*evalReal (ps.map ctx.value) y)
    exact reads_add x0 (ctx.literal (hs p (List.mem_cons_self ..)))
      (reads_mul x0 ctx.root ctx.leading_paid hy (ih (fun p h => hs p (List.mem_cons_of_mem _ h))))

def jacReal (y : R) : R := y*(1+y*(-14+y*(56+y*(-84+42*y))))

def pReal (x0 y : R) : R := jacReal x0*y^3*(10*x0^2+y*(-15*x0+6*y))-x0^5*jacReal y
def nReal {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  2*ctx.value Q*x0+2*((-2)*ctx.value Q+x0*ctx.value S-x0^2)*y
def vReal {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  evalReal ([v0,v1,v2].map ctx.value) y
def qReal {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  evalReal ([q0,q1,q2,q3].map ctx.value) y
def dReal {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  (y^2-ctx.value S*y+ctx.value Q)*(y-26)
def muReal {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  evalReal ([mu0,mu1,mu2,mu3,mu4,mu5,mu6].map ctx.value) y

def evalDiv {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  y^2*(y-x0)^2*vReal ctx y+nReal ctx y*pReal x0 y-dReal ctx y*qReal ctx y
def evalScale {x0 : R} (ctx : ReadContext x0) : R :=
  (26-1)*nReal ctx 26*ctx.value sigma-muReal ctx 26*26*(26-15)*(26-x0)
def evalOut {x0 : R} (ctx : ReadContext x0) (y : R) : R :=
  muReal ctx y*(y-15)*pReal x0 y+(y-1)*y*ctx.value sigma*(y-x0)*vReal ctx y

theorem reads_jac {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (jac x) (jacReal y) := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let aa {a b : Rep} {u v : R} := reads_add x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let nn := reads_nat x0
  unfold jac jacReal
  exact mm hy (aa (nn 1) (mm hy (aa (reads_neg x0 (nn 14))
    (mm hy (aa (nn 56) (mm hy (aa (reads_neg x0 (nn 84)) (mm (nn 42) hy))))))))

theorem reads_p {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (pZ x) (pReal x0 y) := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let aa {a b : Rep} {u v : R} := reads_add x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let bb {a b : Rep} {u v : R} := reads_sub x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let pp {a : Rep} {u : R} := reads_pow x0 ctx.root ctx.leading_paid (a:=a) (x:=u)
  let nn := reads_nat x0
  have hC := reads_c x0
  have hCj := reads_jac ctx hC
  have hYj := reads_jac ctx hy
  unfold pZ pReal
  exact bb (mm (mm hCj (pp hy 3)) (aa (mm (nn 10) (pp hC 2))
    (mm hy (aa (mm (reads_neg x0 (nn 15)) hC) (mm (nn 6) hy)))))
    (mm (pp hC 5) hYj)

theorem reads_n {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (nZ x) (nReal ctx y) := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let aa {a b : Rep} {u v : R} := reads_add x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let bb {a b : Rep} {u v : R} := reads_sub x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let pp {a : Rep} {u : R} := reads_pow x0 ctx.root ctx.leading_paid (a:=a) (x:=u)
  let nn := reads_nat x0
  have hC := reads_c x0
  have hQ := ctx.literal (p:=Q) (by simp [inputSlots])
  have hS := ctx.literal (p:=S) (by simp [inputSlots])
  unfold nZ nReal
  exact aa (mm (mm (nn 2) hQ) hC)
    (mm (mm (nn 2) (bb (aa (mm (reads_neg x0 (nn 2)) hQ) (mm hC hS))
      (pp hC 2))) hy)

theorem reads_d {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (d3 x) (dReal ctx y) := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let aa {a b : Rep} {u v : R} := reads_add x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let bb {a b : Rep} {u v : R} := reads_sub x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let pp {a : Rep} {u : R} := reads_pow x0 ctx.root ctx.leading_paid (a:=a) (x:=u)
  let nn := reads_nat x0
  have hQ := ctx.literal (p:=Q) (by simp [inputSlots])
  have hS := ctx.literal (p:=S) (by simp [inputSlots])
  unfold d3 dReal
  exact mm (aa (bb (pp hy 2) (mm hS hy)) hQ) (bb hy (nn 26))

theorem reads_v {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (vZ x) (vReal ctx y) :=
  reads_eval ctx _ hy (by simp [inputSlots])

theorem reads_q {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (qZ x) (qReal ctx y) :=
  reads_eval ctx _ hy (by simp [inputSlots])

theorem reads_mu {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) : Reads x0 (mu x) (muReal ctx y) :=
  reads_eval ctx _ hy (by simp [inputSlots])

theorem div_read_sound {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) (hz : zero (divGate x)=true) :
    evalDiv ctx y=0 := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let aa {a b : Rep} {u v : R} := reads_add x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let bb {a b : Rep} {u v : R} := reads_sub x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let pp {a : Rep} {u : R} := reads_pow x0 ctx.root ctx.leading_paid (a:=a) (x:=u)
  have hC := reads_c x0
  apply reads_zero x0 _ hz
  have hN := reads_n ctx hy
  have hP := reads_p ctx hy
  have hQ := reads_q ctx hy
  have hV := reads_v ctx hy
  have hD := reads_d ctx hy
  unfold divGate evalDiv
  exact bb (aa (mm (mm (pp hy 2) (pp (bb hy hC) 2)) hV) (mm hN hP)) (mm hD hQ)

theorem div_by_index (i : Fin 7) :
    zero (divGate (OfNat.ofNat (α:=Rep) i.val))=true := by
  have hi := i.isLt
  have h : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 :=
    by omega
  rcases h with h|h|h|h|h|h|h <;> rw [h]
  · exact div_0_exact
  · exact div_1_exact
  · exact div_2_exact
  · exact div_3_exact
  · exact div_4_exact
  · exact div_5_exact
  · exact div_6_exact

/-- Seven paid-site reads suffice for the degree-six residual. This
theorem supplies the seven values without a second decimal check. -/
theorem div_seven_read {x0 : R} (ctx : ReadContext x0) (i : Fin 7) :
    evalDiv ctx (Nat.cast i.val : R)=0 := by
  have h : Reads x0 (OfNat.ofNat (α:=Rep) i.val) (Nat.cast i.val:R) :=
    Eq.mp (congrArg (fun z:R => Reads x0 (OfNat.ofNat (α:=Rep) i.val) z)
      (Semiring.ofNat_eq_natCast i.val)) (reads_nat x0 i.val)
  exact div_read_sound ctx h (div_by_index i)

theorem scale_read_sound {x0 : R} (ctx : ReadContext x0) :
    evalScale ctx=0 := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let bb {a b : Rep} {u v : R} := reads_sub x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let nn := reads_nat x0
  have hC := reads_c x0
  have hsigma := ctx.literal (p:=sigma) (by simp [inputSlots])
  apply reads_zero x0 _ scale_exact
  have hN := reads_n ctx (nn 26)
  have hM := reads_mu ctx (nn 26)
  unfold scaleGate evalScale
  exact bb (mm (mm (bb (nn 26) (nn 1)) hN) hsigma)
    (mm (mm (mm hM (nn 26)) (bb (nn 26) (nn 15))) (bb (nn 26) hC))

theorem out_read_sound {x0 : R} (ctx : ReadContext x0) {x : Rep} {y : R}
    (hy : Reads x0 x y) (hz : zero (outGate x)=true) :
    evalOut ctx y=0 := by
  let mm {a b : Rep} {u v : R} := reads_mul x0 ctx.root ctx.leading_paid
    (a:=a) (b:=b) (x:=u) (y:=v)
  let aa {a b : Rep} {u v : R} := reads_add x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let bb {a b : Rep} {u v : R} := reads_sub x0 (a:=a) (b:=b) (x:=u) (y:=v)
  let nn := reads_nat x0
  have hC := reads_c x0
  have hsigma := ctx.literal (p:=sigma) (by simp [inputSlots])
  apply reads_zero x0 _ hz
  have hM := reads_mu ctx hy
  have hP := reads_p ctx hy
  have hV := reads_v ctx hy
  unfold outGate evalOut
  exact aa (mm (mm hM (bb hy (nn 15))) hP)
    (mm (mm (mm (mm (bb hy (nn 1)) hy) hsigma) (bb hy hC)) hV)

/-- The exact actual normalized e/f output constraints at a decic root. -/
theorem out_e_f_read {x0 : R} (ctx : ReadContext x0) :
    evalOut ctx (ctx.value E)=0 ∧ evalOut ctx (ctx.value F)=0 :=
  ⟨out_read_sound ctx (ctx.literal (by simp [inputSlots])) out_e_exact,
   out_read_sound ctx (ctx.literal (by simp [inputSlots])) out_f_exact⟩

end RKResearch.Certified.ERK10ZTailCore

#print axioms RKResearch.Certified.ERK10ZTailCore.div_seven_read
#print axioms RKResearch.Certified.ERK10ZTailCore.scale_read_sound
#print axioms RKResearch.Certified.ERK10ZTailCore.out_e_f_read
