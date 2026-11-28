module

public import RKCert.ReviewedNative.DIRK12MidpointReversePhysical
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The first three positive reflected primitive tests of the actual
physical reverse matrix. The visible tests need just the normalized
row identities. Global equality needs zero actual ghost projections,
and the paid scalar moments for the origin. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Physical

open RKResearch Graded DualSupport12
open DIRK12MidpointForward DIRK12MidpointForward.Late
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [CharZero K] (P : Feed K) (D : Data K)

local notation "Aphys" => (Feed.tableau (feed P D))
local notation "Yphys" => (reflected (Feed.tableau (feed P D)))

def pastEntry (i : Fin 10) (j : Fin 5) : K :=
  (if head j < i then 0 else P.live (head j) i)*
    P.b (visible (head j))/(D.d*P.b (visible i))

noncomputable def Tread (i : Fin 10) (m : Fin 3) : K :=
  (∑ j : Fin 5, pastEntry P D i j*(Z P D (head j))^(m.val+1))+
    ∑ j : Fin 4, retEntry P D i j*(Groups.sourceClock D.r D.t j)^(m.val+1)

theorem scale_clock (g : Geom P D) (i : Fin 10) :
    Yphys (visible i)=D.d*Z P D i := by
  change 1-nodes Aphys (visible i)=_
  rw [nodes_eq,Z,←mul_div_assoc,mul_div_cancel_left₀ _ g.d0]

private theorem split_visible {S : Type*} [AddCommMonoid S] (w : Fin 10 → S) :
    (∑ j, w j)=((∑ j : Fin 5, w (head j))+
      (∑ j : Fin 4, w (returnRow j)))+w 9 := by
  have p : (∑ j : Fin 5, w (Fin.natAdd 5 j))=(∑ j : Fin 4, w (returnRow j))+w 9 := by
    rw [Fin.sum_univ_add (a:=4) (b:=1)]
    simp only [Fin.sum_univ_one,returnRow]
    rfl
  rw [Fin.sum_univ_add (a:=5) (b:=5),p,add_assoc]
  rfl

theorem physical_read (g : Geom P D) (i : Fin 10) (m : Fin 3) :
    mat (Matrix.transpose Aphys) (moment Aphys P.b (m.val+1)) (visible i)=
      D.d^(m.val+2)*P.b (visible i)*Tread P D i m := by
  change (∑ j : Fin 15, Aphys j (visible i)*(P.b j * Yphys j^(m.val+1)))=_
  rw [sum_stages]
  have u0 : Aphys 0 (visible i)=0 := (feed P D).tableau_origin _
  have zg : (∑ j : Fin 4, Aphys (DIRK12MidpointForward.hidden j) (visible i)*
      (P.b (DIRK12MidpointForward.hidden j) * Yphys (DIRK12MidpointForward.hidden j)^(m.val+1)))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [g.ghost0,zero_mul,mul_zero]
  rw [u0,zero_mul,zg,zero_add,zero_add]
  rw [split_visible (fun j => Aphys (visible j) (visible i)*
      (P.b (visible j)*Yphys (visible j)^(m.val+1)))]
  have term0 : Yphys (visible (9:Fin 10))=0 := by
    change 1-nodes Aphys (visible (9:Fin 10))=0
    rw [nodes_eq,physical_term,g.term1,sub_self]
  rw [term0,zero_pow (by omega : m.val+1≠0),mul_zero,mul_zero,add_zero]
  rw [Tread,mul_add,Finset.mul_sum,Finset.mul_sum]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j _
    rw [head_entry,scale_clock P D g,mul_pow,pastEntry,pow_succ]
    field_simp [g.d0,g.bNZ i]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [return_entry,scale_clock P D g,normalized_return_clock P D g,mul_pow,pow_succ]
    field_simp [g.bNZ (returnRow j)]
    ring

theorem group_read (g : Geom P D) (i : Fin 6) (m : Fin 3) :
    Tread P D (earlyTarget i) m =
      (Z P D (earlyTarget i))^(m.val+2)/((m.val+2:Nat):K)+
        (if m=2 then Seed.lambda D.r*D.h i else 0) := by
  obtain ⟨inj,nz⟩ := Groups.clock_guards g.r0 g.t0 g.r1 g.t1 g.tr
  unfold Tread
  simp only [retEntry_early]
  exact Groups.table_reads inj nz (Z P D (earlyTarget i)) (D.h i) (pastRead P D i) m

theorem seed_clock (g : Geom P D) (i : Fin 3) :
    Z P D (seedTarget i)=Seed.clock D.r i := by
  rw [← return_seed,normalized_return_clock P D g]
  fin_cases i <;> rfl

theorem seed_read (g : Geom P D) (i m : Fin 3) :
    Tread P D (seedTarget i) m =
      (Seed.clock D.r i)^(m.val+2)/((m.val+2:Nat):K)+
        (if m=0 then 0 else if m=1 then Seed.pair i else
          (3/2:K)*Seed.pair i+Seed.lambda D.r*Seed.bary D.r i) := by
  have head0 (j : Fin 5) : pastEntry P D (seedTarget i) j=0 := by
    have e : head j < seedTarget i := by
      change j.val < 6+i.val
      omega
    simp [pastEntry,e]
  unfold Tread
  simp only [head0,zero_mul,Finset.sum_const_zero,zero_add]
  rw [Fin.sum_univ_succ,retEntry_seed0,zero_mul,zero_add]
  have clock (j : Fin 3) : Groups.sourceClock D.r D.t j.succ=Seed.clock D.r j := by
    fin_cases j <;> rfl
  simp only [retEntry_seed,clock]
  fin_cases m
  · simpa using Seed.power1 g.r0 g.r1 g.r2 i
  · simpa using Seed.power2 g.r0 g.r1 g.r2 i
  · simpa [add_assoc] using Seed.power3 g.r0 g.r1 g.r2 i

/-- Unscaled true primitive; indexes 0,1,2 mean entering reflected
degrees 1,2,3 (respectively reverse grades 2,3,4). -/
noncomputable def error (m : Fin 3) : V15 K :=
  mat (Matrix.transpose Aphys) (moment Aphys P.b (m.val+1))-
    (((m.val+2:Nat):K)⁻¹) • moment Aphys P.b (m.val+2)

def expected (m : Fin 3) : V15 K :=
  if m=0 then 0 else if m=1 then G P D else (3*D.d/2) • G P D+Seed.lambda D.r • H P D

theorem error_visible (g : Geom P D) (i : Fin 10) (m : Fin 3) :
    error P D m (visible i)=expected P D m (visible i) := by
  unfold error
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [physical_read P D g]
  rw [show moment Aphys P.b (m.val+2) (visible i)=
      P.b (visible i)*(D.d*Z P D i)^(m.val+2) by
        change P.b (visible i)*Yphys (visible i)^(m.val+2)=_
        rw [scale_clock P D g]]
  rw [mul_pow]
  revert i
  apply target_cases
  · intro i
    rw [group_read P D g]
    have pp := pair_early P D i
    change G P D (visible (earlyTarget i))=0 at pp
    fin_cases m <;> norm_num [Fin.ext_iff,expected,pp,hv,ampl_early] <;> ring
  · intro i
    rw [seed_read P D g,seed_clock P D g]
    have pp := pair_seed P D g i
    change G P D (visible (seedTarget i))=
      D.d^3*P.b (visible (seedTarget i))*Seed.pair i at pp
    fin_cases m <;> norm_num [Fin.ext_iff,expected,pp,hv,ampl_seed] <;> ring
  · have t0 : Z P D 9=0 := by rw [Z,physical_term,g.term1,sub_self,zero_div]
    have heads : (∑ j : Fin 5, pastEntry P D 9 j*(Z P D (head j))^(m.val+1))=0 := by
      apply Finset.sum_eq_zero
      intro j _
      have e : head j < (9:Fin 10) := by
        change j.val < 9
        omega
      simp [pastEntry,e]
    simp only [Tread,heads,retEntry_end,zero_mul,Finset.sum_const_zero,add_zero,t0,
      zero_pow (by omega : m.val+2≠0),mul_zero,sub_self]
    have ht : H P D terminal=0 := by rw [←physical_term,H_visible,hv,ampl_terminal,mul_zero]
    fin_cases m <;> simp [expected,G,physicalPair,ht,
      show terminal≠(13:Fin 15) by decide,show terminal≠(11:Fin 15) by decide]

theorem error_sum (m : Fin 3)
    (scalar : ∀ j < 12, ((j+1:Nat):K)*row P.b ((nodes Aphys)^j)=1) :
    (∑ i, error P D m i)=0 := by
  let j := m.val+1
  have sc := mixed_scalar Aphys P.b scalar j 0 (by dsimp [j]; omega)
  have h : row (moment Aphys P.b (j+1)) (1:V15 K)=
      ((j+1:Nat):K)*row (moment Aphys P.b j) (nodes Aphys) := by simpa using sc
  have tr (z : V15 K) : row (mat (Matrix.transpose Aphys) z) (1:V15 K)=row z (nodes Aphys) := by
    rw [row_apply,row_apply,mat_apply,dotProduct_comm,Matrix.dotProduct_transpose_mulVec]
  have subL (v w : V15 K) : row (v-w) (1:V15 K)=row v (1:V15 K)-row w (1:V15 K) := by simp
  have mulL (a : K) (v : V15 K) : row (a • v) (1:V15 K)=a*row v (1:V15 K) := by simp
  have out : row (error P D m) (1:V15 K)=0 := by
    change row (mat (Matrix.transpose Aphys) (moment Aphys P.b j)-
      (((j+1:Nat):K)⁻¹) • moment Aphys P.b (j+1)) (1:V15 K)=0
    rw [subL,mulL,tr,h,inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (by omega)),sub_self]
  simpa [row_apply,dotProduct] using out

theorem expected_sum (m : Fin 3) : (∑ i, expected P D m i)=0 := by
  fin_cases m <;> simp [expected,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,G_sum]

theorem expected_ghost (m : Fin 3) (i : Fin 4) :
    expected P D m (DIRK12MidpointForward.hidden i)=0 := by
  fin_cases m <;> simp [expected,G_hidden]

theorem error_vector (g : Geom P D)
    (scalar : ∀ j < 12, ((j+1:Nat):K)*row P.b ((nodes Aphys)^j)=1)
    (m : Fin 3) (gh : ∀ i : Fin 4, error P D m (DIRK12MidpointForward.hidden i)=0) :
    error P D m=expected P D m := by
  have q (i : Fin 4) := (gh i).trans (expected_ghost P D m i).symm
  have p := fun i => error_visible P D g i m
  have o := sum_eq_origin _ _ ((error_sum P D m scalar).trans (expected_sum P D m).symm) q p
  funext i
  exact stage_cases (P:=fun i => error P D m i=expected P D m i) o q p i

end RKResearch.Certified.DIRK12MidpointReverse.Physical

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Physical.physical_read
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Physical.error_visible
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Physical.error_vector
