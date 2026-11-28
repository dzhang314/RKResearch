#!/usr/bin/env python3
"""Generate the four-chart kernel-verified ERK10 ring-domain assembly."""
from pathlib import Path
from argparse import ArgumentParser
from fractions import Fraction
from functools import reduce
from math import factorial, lcm, gcd
import json

PORTFOLIO = Path('ai-generated/research/erk10-sixteen-rational-portfolio')
CHARTS = (
    ("ERK10RationalSixteen", "../erk10-sixteen-rational-mirror/tableau.json"),
    ("ERK10MirrorCompact", "theta-five-fourths.json"),
    ("ERK10MirrorThetaFour", "theta-four.json"),
    ("ERK10MirrorUnit13", "denominator-unit-at-13.json"),
)

def denom(file):
    data=json.loads((PORTFOLIO/file).read_text())
    return lcm(*(Fraction(x).denominator for row in [*data['A'],data['b']] for x in row))

def bezout(dens):
    g=dens[0]
    e=[1]
    for d in dens[1:]:
        old=g
        g=gcd(old,d)
        j=(pow(old//g,-1,d//g) if d//g != 1 else 0)
        k=(g-old*j)//d
        assert old*j+d*k==g
        e=[a*j for a in e]+[k]
    return e,g

def adapters():
    scripts=[]
    for i,(ns,_) in enumerate(CHARTS):
        scripts.append(f"""private theorem pair{i} {{R : Type*}} [CommRing R]
    (hD : IsUnit ({ns}.D : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : ({ns}.D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact PairCert.of_integer_receipts
    ({ns}.explicit d) ({ns}.order_ten d hd)
    {ns}.d₁ {ns}.d₂ {ns}.n₁ {ns}.n₂ {ns}.e₁ {ns}.e₂
    ({ns}.from_integer_defect {ns}.tree₁ (by decide) _ _ {ns}.integer_next₁ d hd)
    ({ns}.from_integer_defect {ns}.tree₂ (by decide) _ _ {ns}.integer_next₂ d hd) {ns}.bezout
""")
    return "\n".join(scripts)

def emit():
    ds=[denom(file) for _,file in CHARTS]
    es,g=bezout(ds)
    assert g==816480000 and sum(e*d for e,d in zip(es,ds))==g
    assert factorial(10)**2%g==0
    imports="".join(f"public import RKCert.ReviewedNative.{c}\n" for c,_ in CHARTS)
    pairs=",\n   ".join(f"({e}, {d})" for e,d in zip(es,ds))
    sections="\n".join(f"  · exact {c}.exists_exact_of_unit (int_unit_of_nat _ unit)"
                       for c,_ in CHARTS)
    pair_sections="\n".join(f"  · exact pair{i} (int_unit_of_nat _ unit)"
                            for i in range(len(CHARTS)))
    return f"""module

{imports}public import RKCert.ReviewedNative.RobustExplicitPair

@[expose] public section

/-! Four concrete rational tableaux cover all admissible local and positive
characteristic rings. This proves no single generic factorial-localized tableau. -/
namespace RKResearch.Certified.ERK10MirrorPortfolio

open ExactExplicitPortfolio

def chartTerms : List (Int × Nat) :=
  [{pairs}]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem literal_bezout :
    (chartTerms.map (fun term => term.1 * (term.2 : Int))).sum = (816480000 : Int) := by
  decide +kernel

private theorem int_unit_of_nat {{R : Type*}} [CommRing R] (d : Nat)
    (h : IsUnit (d : R)) : IsUnit ((d : Int) : R) := by
  simpa only [Int.cast_natCast] using h

set_option maxRecDepth 50000 in
theorem local_exact (R : Type*) [CommRing R] [IsLocalRing R]
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) : Exact 16 10 R := by
  have hdiv : (816480000 : Nat) ∣ (Nat.factorial 10)^2 := by decide +kernel
  have hp : IsUnit (((Nat.factorial 10)^2 : Nat) : R) := by
    simpa only [Nat.cast_pow] using hf.pow 2
  have hg : IsUnit (((816480000 : Nat)) : R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := R) hdiv) hp
  refine local_exact_of_denominators chartTerms literal_bezout hg ?_
  intro term hit unit
  simp only [chartTerms, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
{sections}

{adapters()}

theorem clean_ring_pair (R : Type*) [CommRing R] (hc : Clean (T := R))
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  have hdiv : (816480000 : Nat) ∣ (Nat.factorial 10)^2 := by decide +kernel
  have hp : IsUnit (((Nat.factorial 10)^2 : Nat) : R) := by
    simpa only [Nat.cast_pow] using hf.pow 2
  have hg : IsUnit (((816480000 : Nat)) : R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := R) hdiv) hp
  refine PairCert.clean_of_bezout hc chartTerms literal_bezout hg ?_
  intro S _ term hit unit
  simp only [chartTerms, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
{pair_sections}

theorem clean_ring_exact (R : Type*) [CommRing R] [Nontrivial R]
    (hc : Clean (T := R)) (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) :
    Exact 16 10 R :=
  (clean_ring_pair R hc hf).exact (by decide) (by decide)

theorem clean_coefficients_exact {{R S : Type*}} [CommRing R] [CommRing S] [Nontrivial S]
    (hc : Clean (T := R)) (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) (f : R →+* S) :
    Exact 16 10 S :=
  ((clean_ring_pair R hc hf).map f).exact (by decide) (by decide)

theorem positive_characteristic_exact (R : Type*) [CommRing R] [Nontrivial R]
    (n : Nat) [CharP R n] (hn : 0 < n)
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) : Exact 16 10 R :=
  positive_characteristic_of_local_unit (Nat.factorial 10) n hn hf
    (fun T _ _ hfT => local_exact T hfT)

end RKResearch.Certified.ERK10MirrorPortfolio

#print axioms RKResearch.Certified.ERK10MirrorPortfolio.local_exact
#print axioms RKResearch.Certified.ERK10MirrorPortfolio.positive_characteristic_exact
#print axioms RKResearch.Certified.ERK10MirrorPortfolio.clean_ring_exact
#print axioms RKResearch.Certified.ERK10MirrorPortfolio.clean_coefficients_exact
"""

if __name__=='__main__':
    p=ArgumentParser()
    p.add_argument('emit',type=Path)
    p.parse_args().emit.write_text(emit())
