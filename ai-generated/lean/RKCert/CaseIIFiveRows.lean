module

public import RKCert.CaseIIScalars

@[expose] public section

/-! # Physical first-five-row obstruction when the quadratic defect lives at node one -/
namespace RKCert.Paired.CaseII
open RKCert.Paired
variable {K : Type*} [Field K]

theorem mat5_at0 {A : Fin 5  →  Fin 5  →  K} (ha : StrictLower A) (x : Vec K 5) :
    mat A x 0 = 0 := by
  rw [mat_apply,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 0 0*x 0+(A 0 1*x 1+(A 0 2*x 2+(A 0 3*x 3+(A 0 4*x 4+(0))))) = _
  rw [ha 0 0 (by decide),ha 0 1 (by decide),ha 0 2 (by decide),ha 0 3 (by decide),ha 0 4 (by decide)]
  ring

theorem mat5_at1 {A : Fin 5  →  Fin 5  →  K} (ha : StrictLower A) (x : Vec K 5) :
    mat A x 1 = A 1 0*x 0 := by
  rw [mat_apply,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 1 0*x 0+(A 1 1*x 1+(A 1 2*x 2+(A 1 3*x 3+(A 1 4*x 4+(0))))) = _
  rw [ha 1 1 (by decide),ha 1 2 (by decide),ha 1 3 (by decide),ha 1 4 (by decide)]
  ring

theorem mat5_at2 {A : Fin 5  →  Fin 5  →  K} (ha : StrictLower A) (x : Vec K 5) :
    mat A x 2 = A 2 0*x 0+A 2 1*x 1 := by
  rw [mat_apply,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 2 0*x 0+(A 2 1*x 1+(A 2 2*x 2+(A 2 3*x 3+(A 2 4*x 4+(0))))) = _
  rw [ha 2 2 (by decide),ha 2 3 (by decide),ha 2 4 (by decide)]
  ring

theorem mat5_at3 {A : Fin 5  →  Fin 5  →  K} (ha : StrictLower A) (x : Vec K 5) :
    mat A x 3 = A 3 0*x 0+A 3 1*x 1+A 3 2*x 2 := by
  rw [mat_apply,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 3 0*x 0+(A 3 1*x 1+(A 3 2*x 2+(A 3 3*x 3+(A 3 4*x 4+(0))))) = _
  rw [ha 3 3 (by decide),ha 3 4 (by decide)]
  ring

theorem mat5_at4 {A : Fin 5  →  Fin 5  →  K} (ha : StrictLower A) (x : Vec K 5) :
    mat A x 4 = A 4 0*x 0+A 4 1*x 1+A 4 2*x 2+A 4 3*x 3 := by
  rw [mat_apply,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 4 0*x 0+(A 4 1*x 1+(A 4 2*x 2+(A 4 3*x 3+(A 4 4*x 4+(0))))) = _
  rw [ha 4 4 (by decide)]
  ring

variable [CharZero K]

/-- The needed low-grade tests on the five chronological rows. No ambient order or
independence condition is hidden in this intermediate statement. -/
theorem five_rows_impossible {A : Fin 5  →  Fin 5  →  K} (ha : StrictLower A)
    (c d w : Vec K 5) (hc : c=nodes A) (h1 : c 1=1)
    (hd : ∀i,d i=mat A c i-c i^2/2) (hw : w=mat A d)
    (hs : ∀i,d i=0 ∨ c i=1 ∧ d i= -(1/2:K))
    (sep : ∀i j : Fin 5, i<j  →  c j=c i  →  d j=d i  →  w j=w i  →  False)
    (p3 : ∃a b : K, ∀i, 3*mat A (c^2) i-c i^3=a*d i+b*w i)
    (aw : ∃a b k : K, ∀i, mat A w i=a*d i+(b+k*c i)*w i)
    (pq : ∀ t y : K, ∃a b e : K, ∀i,
       mat A (fun j => DQ t y (c j)) i-Q t y (c i)=a*d i+(b+e*c i)*w i)
    (acw : ∃a : K, ∃g : K → K, ∀i, mat A (fun j => c j*w j) i=a*d i+g (c i)*w i) :
    False := by
  have hc0 : c 0=0 := by rw [hc]; simpa [nodes,mat_apply] using mat5_at0 ha (1:Vec K 5)
  have hd0 : d 0=0 := by rw [hd,mat5_at0 ha,hc0]; ring
  have hd1 : d 1= -(1/2:K) := by rw [hd,mat5_at1 ha,h1,hc0]; ring
  have hw0 : w 0=0 := by rw [hw,mat5_at0 ha]
  have hw1 : w 1=0 := by rw [hw,mat5_at1 ha,hd0,mul_zero]
  have d2 := hd 2
  rw [mat5_at2 ha,hc0,h1,mul_zero,zero_add,mul_one] at d2
  have w2 : w 2= -A 2 1/2 := by rw [hw,mat5_at2 ha,hd0,hd1]; ring
  have die0 (i : Fin 5) (hi : 0 < i) : c i=0 → d i=0 → w i=0 → False :=
    fun hx dx wx => sep 0 i hi (hx.trans hc0.symm) (dx.trans hd0.symm) (wx.trans hw0.symm)
  have die1 (i : Fin 5) (hi : 1 < i) : c i=1 → d i= -(1/2:K) → w i=0 → False :=
    fun hx dx wx => sep 1 i hi (hx.trans h1.symm) (dx.trans hd1.symm) (wx.trans hw1.symm)
  obtain ⟨hd2,ht,ha21,hw2⟩ := third_row _ _ _ _ d2 w2 (hs 2) (die0 2 (by decide)) (die1 2 (by decide))
  have dieT (i : Fin 5) (hi : 2 < i) : c i=c 2 → d i=0 → w i= -(c 2^2)/4 → False :=
    fun hx dx wx => sep 2 i hi hx (dx.trans hd2.symm) (wx.trans hw2.symm)
  obtain ⟨u,v,hcubic⟩ := p3
  have hC1 := hcubic 1
  rw [mat5_at1 ha] at hC1
  simp only [Pi.pow_apply,hc0,h1,hd1,hw1] at hC1
  have hC2 := hcubic 2
  rw [mat5_at2 ha] at hC2
  simp only [Pi.pow_apply,hc0,h1,hd2,hw2] at hC2
  obtain ⟨rfl,rfl⟩ := cubic_calibration (c 2) (A 2 1) u v ht ha21
    (by linear_combination hC1) (by linear_combination hC2)
  have d3 := hd 3
  rw [mat5_at3 ha,hc0,h1,mul_zero,zero_add,mul_one] at d3
  have w3 : w 3= -A 3 1/2 := by rw [hw,mat5_at3 ha,hd0,hd1,hd2]; ring
  have hC3 := hcubic 3
  rw [mat5_at3 ha] at hC3
  simp only [Pi.pow_apply,hc0,h1] at hC3
  obtain ⟨hd3,hz,hzt,h31,h32⟩ := fourth_row (c 2) (c 3) (A 3 1) (A 3 2) (d 3) (w 3) ht
    (by linear_combination d3) w3 (by linear_combination hC3) (hs 3)
    (die0 3 (by decide)) (die1 3 (by decide)) (dieT 3 (by decide))
  obtain ⟨l,b,k,hAw⟩ := aw
  have hA1 := hAw 1
  rw [mat5_at1 ha,hw0,hd1,hw1] at hA1
  have hl : l=0 := by linear_combination 2*hA1
  subst l
  have hA2 := hAw 2
  rw [mat5_at2 ha,hw0,hw1,hw2] at hA2
  have hcoef : b= -k*c 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ht)
    linear_combination 4*hA2
  subst b
  have hZ := hAw 3
  rw [mat5_at3 ha,hw0,hw1,hw2] at hZ
  have hAZ : A 3 2 * (-(c 2^2)/4) = k*(c 3-c 2)*w 3 := by linear_combination hZ
  obtain ⟨hw3,hW,hk⟩ := tap_calibration _ _ _ _ _ _ ht hz hzt h31 h32 w3 hAZ
  have w4 : w 4= -A 4 1/2 := by rw [hw,mat5_at4 ha,hd0,hd1,hd2,hd3]; ring
  have hY := hAw 4
  rw [mat5_at4 ha,hw0,hw1,hw2] at hY
  have hAY : A 4 2 * (-(c 2^2)/4)+A 4 3*w 3=k*(c 4-c 2)*w 4 := by linear_combination hY
  obtain ⟨a,b,e,hQ⟩ := pq (c 2) (c 4)
  have hQ1 := hQ 1
  rw [mat5_at1 ha,hc0,h1,hd1,hw1] at hQ1
  have haQ : a=2*Q (c 2) (c 4) 1 := by
    simp only [DQ, mul_zero,zero_pow (by decide : 3≠0), zero_pow (by decide : 2≠0),
      sub_zero,add_zero,zero_sub] at hQ1
    linear_combination 2*hQ1
  subst a
  have hQ2 := hQ 2; have hQ3 := hQ 3; have hQ4 := hQ 4
  rw [mat5_at2 ha,hc0,h1,hd2,hw2,ha21] at hQ2
  rw [mat5_at3 ha,hc0,h1,hd3] at hQ3
  rw [mat5_at4 ha,hc0,h1] at hQ4
  have hq5 : Q (c 2) (c 4) 1 * d 4=0 := by
    rcases hs 4 with h|⟨h,_⟩
    · rw [h,mul_zero]
    · simp [Q,h]
  have hD0 : DQ (c 2) (c 4) 0=0 := by simp [DQ]
  have hQy : Q (c 2) (c 4) (c 4)=0 := by simp [Q]
  rw [hD0] at hQ2 hQ3 hQ4
  have hcut := terminal_tap_or_repeat (c 2) (c 3) (c 4) k b e (w 3) (w 4) (A 3 1)
    (A 3 2) (A 4 1) (A 4 2) (A 4 3) ht hz hzt hw3 hW hAZ hAY
    (by linear_combination 2*w3) (by linear_combination 2*w4)
    (by linear_combination hQ2) (by linear_combination hQ3)
    (by rw [hQy] at hQ4; linear_combination hQ4+2*hq5)
  have hn : A 4 3≠0 := by
    intro h
    have d4 := hd 4
    rw [mat5_at4 ha,hc0,h1,h] at d4
    have hC4 := hcubic 4
    rw [mat5_at4 ha,h] at hC4
    simp only [Pi.pow_apply,hc0,h1] at hC4
    rw [h,zero_mul,add_zero] at hAY
    exact no_zero_tap (c 2) (c 3) (c 4) k (w 3) (w 4) (A 4 1) (A 4 2) (d 4) ht hW hk
      (by linear_combination d4) w4 (by linear_combination hC4) hAY (hs 4)
      (die0 4 (by decide)) (die1 4 (by decide)) (dieT 4 (by decide))
      (fun hx dx wx => sep 3 4 (by decide) hx (dx.trans hd3.symm) wx)
  have hyz := hcut.resolve_left hn
  obtain ⟨α,g,hCg⟩ := acw
  have hg1 := hCg 1
  rw [mat5_at1 ha,hc0,hd1,hw1] at hg1
  have he : α=0 := by linear_combination 2*hg1
  subst α
  have hg3 := hCg 3; have hg4 := hCg 4
  rw [mat5_at3 ha,hw0,hw1,hw2] at hg3
  rw [mat5_at4 ha,hw0,hw1,hw2,hyz] at hg4
  rw [hyz] at hAY
  exact repeat_contradiction (c 2) (c 3) k (g (c 3)) (w 3) (w 4) (A 3 2) (A 4 2)
    (A 4 3) hzt hw3 hn hAZ hAY (by linear_combination hg3) (by linear_combination hg4)

end RKCert.Paired.CaseII
