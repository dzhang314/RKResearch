"""Generate an arithmetic-only Lean Core replay of the exact native flag data."""
import argparse
from pathlib import Path

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("lean_data",type=Path)
    cli.add_argument("output",type=Path)
    x=cli.parse_args()
    source=x.lean_data.read_text()
    native=source[source.index("def a0"):source.index("def packet")].replace("ℚ","Rat").replace("ℕ","Nat")
    first="""import Lean
import Init.Data.Rat.Basic

set_option maxHeartbeats 0
set_option maxRecDepth 50000
namespace DIRK10TwelvePortableFlagArithmetic

"""
    checks="""
def size (d : Nat) : Nat := sizes.getD d 0
def aug (d i j : Nat) : Rat := ((bases.getD d #[]).getD i #[]).getD j 0
def a (i j : Nat) : Rat := (a0.getD i #[]).getD j 0
def b (i : Nat) : Rat := b0.getD i 0
def c (i : Nat) : Rat := c0.getD i 0
def sum (n : Nat) (f : Nat → Rat) : Rat := ((List.range n).map f).foldr (·+·) 0
def act (v : Nat → Rat) (i : Nat) : Rat := sum 12 (fun j => a i j*v j)
def out (v : Nat → Rat) : Rat := sum 12 (fun i => b i*v i)
def cp (v w : Nat → Rat) (i : Nat) : Rat := v i*w i
def project (d : Nat) (v : Nat → Rat) (i : Nat) : Rat :=
  sum (size d) (fun j => v ((pivots.getD d #[]).getD j 0) * aug d j i)
def shape : Bool := (List.range 12).all fun i =>
  (List.range 12).all fun j => decide (i < j → a i j=0)
def veq (v w : Nat → Rat) : Bool := (List.range 12).all fun i => decide (v i=w i)
def synth (d : Nat) (v : Nat → Rat) : Bool := veq v (project d v)
def evolve (d : Nat) : Bool := (List.range (size d)).all fun i =>
  synth (d+1) (act (aug d i)) && synth (d+1) (cp c (aug d i))
def pay (d : Nat) : Bool :=
  decide ((d+1:Rat) * out (fun i => c i ^ d) = 1) &&
  (List.range (size d)).all fun i => decide (out (aug d i)=0)
def prim (d : Nat) : Bool :=
  synth (d+1) (fun i => (d+1:Rat) * act (fun j => c j ^ d) i - c i ^ (d+1))
def prodBand (d e : Nat) : Bool := (List.range (size d)).all fun i =>
  (List.range (size e)).all fun j => synth (d+e) (cp (aug d i) (aug e j))

theorem check_shape : shape=true := by decide +kernel
theorem check_clocks : veq c (act (fun _ => 1))=true := by decide +kernel
theorem check_star : 11 * out (fun i => c i ^ (10:Nat)) - 1=(1:Rat)/2488320 := by decide +kernel
"""
    for d in range(10):
        checks+=f"theorem pay_{d} : pay {d}=true := by decide +kernel\n"
        if d<9:
            checks+=f"theorem evolve_{d} : evolve {d}=true := by decide +kernel\n"
            checks+=f"theorem prim_{d} : prim {d}=true := by decide +kernel\n"
        for e in range(10-d):
            checks+=f"theorem prod_{d}_{e} : prodBand {d} {e}=true := by decide +kernel\n"
    checks+="\n#print axioms check_star\n#print axioms evolve_8\n#print axioms prod_3_6\n\nend DIRK10TwelvePortableFlagArithmetic\n"
    x.output.write_text(first+native+checks)

if __name__=="__main__":main()
