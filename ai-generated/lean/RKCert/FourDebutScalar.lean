module
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace RKCert.FourDebut
variable {K : Type*} [Field K] [CharZero K]

/-- Coordinates of actual primitives of xV2, xV3, x²V3. -/
def L2 (a b x : K) : K := x^2/4-(a+b)*x/3+a*b/2
def B1 (a b u x : K) : K :=
  x^5/5-(a+b+u)*x^4/4+(a*b+u*(a+b))*x^3/3-a*b*u*x^2/2
def B2 (a b u x : K) : K :=
  x^6/6-(a+b+u)*x^5/5+(a*b+u*(a+b))*x^4/4-a*b*u*x^3/3

omit [CharZero K] in
/-- Vanishing of a quadratic at three arbitrary, pairwise distinct field elements. -/
theorem quad3 {a b u A B C : K} (hab : a≠b) (hbu : b≠u) (hau : a≠u)
    (ha : A*a^2+B*a+C=0) (hb : A*b^2+B*b+C=0) (hu : A*u^2+B*u+C=0) :
    A=0 ∧ B=0 ∧ C=0 := by
  have diff (x y : K) (hne : x≠y) (hx : A*x^2+B*x+C=0) (hy : A*y^2+B*y+C=0) :
      A*(x+y)+B=0 :=
    (mul_eq_zero.mp (show (x-y)*(A*(x+y)+B)=0 by linear_combination hx-hy)).resolve_left (sub_ne_zero.mpr hne)
  have ab := diff a b hab ha hb
  have bu := diff b u hbu hb hu
  have ha0 : A=0 := (mul_eq_zero.mp (show A*(a-u)=0 by linear_combination ab-bu)).resolve_right (sub_ne_zero.mpr hau)
  rw [ha0,zero_mul,zero_add] at ab
  exact ⟨ha0,ab,by simpa [ha0,ab] using ha⟩

/-- Direct free-clock reconstruction of the first three knots from the two
barycentric constraints and the actual primitive of xV2. No root ordering,
complex embedding, or prescribed Jacobi grid. -/
theorem first_three {a b u v wa wb wu h : K}
    (ha : a≠0) (hb : b≠0) (hu : u≠0) (hab : a≠b) (hau : a≠u) (hbu : b≠u) (huv : u≠v)
    (hwa : wa≠0) (hwb : wb≠0) (hwu : wu≠0)
    (c3 : (a^2/wa)*(a-u)+(b^2/wb)*(b-u)=0)
    (c4 : (a^2/wa)*(a-v)+(b^2/wb)*(b-v)+(u^2/wu)*(u-v)=0)
    (q0 : a^2*L2 a b a=wa*h) (q1 : b^2*L2 a b b=wb*h) (q2 : u^2*L2 a b u=wu*h) :
    ∃ E:K, E≠0 ∧ a+b=u ∧ 5*(a*b)=u^2 ∧
      wa*E = a^2*(a-b)*(a-u) ∧ wb*E=b^2*(b-a)*(b-u) ∧ wu*E=u^2*(u-a)*(u-b) := by
  let r := a^2/wa
  let s := b^2/wb
  let t := u^2/wu
  change r*(a-u)+s*(b-u)=0 at c3
  change r*(a-v)+s*(b-v)+t*(u-v)=0 at c4
  have total : r+s+t=0 := (mul_eq_zero.mp
    (show (u-v)*(r+s+t)=0 by linear_combination c4-c3)).resolve_left (sub_ne_zero.mpr huv)
  have two : r*(a-b)+t*(u-b)=0 := by linear_combination c3+(u-b)*total
  let E := r*(a-b)*(a-u)
  have e0 : E ≠ 0 := mul_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero _ ha) hwa) (sub_ne_zero.mpr hab)) (sub_ne_zero.mpr hau)
  have es : E=s*(b-a)*(b-u) := by dsimp [E]; linear_combination (a-b)*c3
  have et : E=t*(u-a)*(u-b) := by dsimp [E]; linear_combination (a-u)*two
  have ea : wa*E=a^2*(a-b)*(a-u) := by dsimp [E,r]; field_simp
  have eb : wb*E=b^2*(b-a)*(b-u) := by rw [es]; dsimp [s]; field_simp
  have eu : wu*E=u^2*(u-a)*(u-b) := by rw [et]; dsimp [t]; field_simp
  have collect (x y D : K) (hx : x≠0) (e : y*E = x^2*D) (f : x^2*L2 a b x = y*h) :
      E*L2 a b x=h*D := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hx)
    calc
      x^2*(E*L2 a b x) = (x^2*L2 a b x)*E := by ring
      _ = h*(y*E) := by rw [f]; ring
      _ = x^2*(h*D) := by rw [e]; ring
  have a0 := collect a wa ((a-b)*(a-u)) ha (by rw [ea]; ring) q0
  have b0 := collect b wb ((b-a)*(b-u)) hb (by rw [eb]; ring) q1
  have u0 := collect u wu ((u-a)*(u-b)) hu (by rw [eu]; ring) q2
  simp only [L2] at a0 b0 u0
  let aa:=E/4-3*h
  let bb:= -E*(a+b)/3+2*h*(a+b+u)
  let cc:= E*(a*b)/2-h*(a*b+u*(a+b))
  obtain ⟨qa,qb,qc⟩ := quad3 (A:=aa) (B:=bb) (C:=cc) hab hbu hau
    (by dsimp [aa,bb,cc]; linear_combination a0)
    (by dsimp [aa,bb,cc]; linear_combination b0)
    (by dsimp [aa,bb,cc]; linear_combination u0)
  dsimp [aa,bb,cc] at qa qb qc
  have eqE : E=12*h := by linear_combination 4*qa
  have h0 : h≠0 := fun ez => e0 (by rw [eqE,ez,mul_zero])
  rw [eqE] at qb qc
  have sum : a+b=u := sub_eq_zero.mp <| (mul_eq_zero.mp (show h*((a+b)-u)=0 by
    linear_combination (-1/2:K)*qb)).resolve_left h0
  rw [sum] at qc
  have prod : 5*(a*b)=u^2 := sub_eq_zero.mp <| (mul_eq_zero.mp (show h*(5*(a*b)-u^2)=0 by
    linear_combination qc)).resolve_left h0
  exact ⟨E,e0,sum,prod,ea,eb,eu⟩

/-- The last two primitive-vs-head interpolation conditions cannot both hold
at a fourth distinct nonzero clock. The fourth head amplitude may be zero. -/
theorem fourth_impossible {a b u v wa wb wu wv h l₁ l₀ q₂ q₁ q₀ : K}
    (ha : a≠0) (hb : b≠0) (hu : u≠0) (hv : v≠0)
    (hab : a≠b) (hau : a≠u) (hbu : b≠u) (hav : a≠v) (hbv : b≠v) (huv : u≠v)
    (hwa : wa≠0) (hwb : wb≠0) (hwu : wu≠0)
    (c3 : (a^2/wa)*(a-u)+(b^2/wb)*(b-u)=0)
    (c4 : (a^2/wa)*(a-v)+(b^2/wb)*(b-v)+(u^2/wu)*(u-v)=0)
    (p0 : a^2*L2 a b a=wa*h) (p1 : b^2*L2 a b b=wb*h) (p2 : u^2*L2 a b u=wu*h)
    (tr : ∀ x w, (x=a ∧ w=wa) ∨ (x=b ∧ w=wb) ∨ (x=u ∧ w=wu) ∨ (x=v ∧ w=wv) →
      B1 a b u x=w*(l₁*x+l₀) ∧ B2 a b u x=w*(q₂*x^2+q₁*x+q₀)) : False := by
  obtain ⟨E,_,sum,prod,ea,eb,_⟩ := first_three ha hb hu hab hau hbu huv hwa hwb hwu c3 c4 p0 p1 p2
  have ab : a*b=u^2/5 := by linear_combination (1/5:K)*prod
  have H1 (x : K) : B1 a b u x=x^2*(x-u)^2*(2*x-u)/10 := by
    rw [B1,sum,ab]; ring
  have H2 (x : K) : B2 a b u x=x^3*(x-u)^2*(5*x-2*u)/30 := by
    rw [B2,sum,ab]; ring
  have atInterior (x w : K) (hw : w≠0)
      (rot : 5*x^2-5*u*x+u^2=0) (weight : w*E=x^2*(x-u)*(2*x-u))
      (h1 : B1 a b u x=w*(l₁*x+l₀)) (h2 : B2 a b u x=w*(q₂*x^2+q₁*x+q₀)) :
      l₁*x+l₀=E*(x-u)/10 ∧ q₂*x^2+q₁*x+q₀=E*(x-u)*(5*x-u)/30 := by
    rw [H1] at h1; rw [H2] at h2
    constructor
    · apply mul_left_cancel₀ hw
      linear_combination -h1 - ((x-u)/10)*weight
    · apply mul_left_cancel₀ hw
      linear_combination -h2 - ((x-u)*(5*x-u)/30)*weight - (x^2*(x-u)^2/30)*rot
  obtain ⟨h1a,h2a⟩ := tr a wa (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨h1b,h2b⟩ := tr b wb (Or.inr (Or.inl ⟨rfl,rfl⟩))
  obtain ⟨h1u,h2u⟩ := tr u wu (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
  obtain ⟨h1v,h2v⟩ := tr v wv (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩)))
  obtain ⟨la,qa⟩ := atInterior a wa hwa (by linear_combination 5*a*sum-prod)
    (by rw [ea,←sum]; ring) h1a h2a
  obtain ⟨lb,qb⟩ := atInterior b wb hwb (by linear_combination 5*b*sum-prod)
    (by rw [eb,←sum]; ring) h1b h2b
  have lu : l₁*u+l₀=0 := by
    rw [H1,sub_self] at h1u
    exact (mul_eq_zero.mp (by simpa using h1u.symm)).resolve_left hwu
  have qu : q₂*u^2+q₁*u+q₀=0 := by
    rw [H2,sub_self] at h2u
    exact (mul_eq_zero.mp (by simpa using h2u.symm)).resolve_left hwu
  obtain ⟨_,f1,f0⟩ := quad3 (A:=0) (B:=l₁-E/10) (C:=l₀+E*u/10) hab hbu hau
    (by linear_combination la) (by linear_combination lb) (by linear_combination lu)
  obtain ⟨f2',f1',f0'⟩ := quad3 (A:=q₂-E/6) (B:=q₁+E*u/5) (C:=q₀-E*u^2/30) hab hbu hau
    (by linear_combination qa) (by linear_combination qb) (by linear_combination qu)
  have lv : l₁*v+l₀=E*(v-u)/10 := by linear_combination v*f1+f0
  have qv : q₂*v^2+q₁*v+q₀=E*(v-u)*(5*v-u)/30 := by
    linear_combination v^2*f2'+v*f1'+f0'
  have vanish : B1 a b u v*((v-u)*(5*v-u)/30)-B2 a b u v*((v-u)/10)=0 := by
    rw [h1v,h2v,lv,qv]; ring
  rw [H1,H2] at vanish
  have zz : v^2*(v-u)^3*(5*v^2-5*u*v+u^2)=0 := by linear_combination 300*vanish
  have fac : 5*v^2-5*u*v+u^2=5*(v-a)*(v-b) := by rw [←prod,←sum]; ring
  rw [fac] at zz
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hv) (pow_ne_zero _ (sub_ne_zero.mpr huv.symm)))
    (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hav.symm)) (sub_ne_zero.mpr hbv.symm))) zz

end RKCert.FourDebut
