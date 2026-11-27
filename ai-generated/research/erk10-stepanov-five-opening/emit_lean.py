"""Emit kernel modular determinant receipts from the independently rebuilt matrices."""
import ast, pathlib, subprocess, sys
code=subprocess.check_output([sys.executable,"defect_gates.py","stepanov15-source.txt","--lean-source"],text=True)
start="""import Lean

namespace RKResearch.ERK10StepanovFiveOpeningMod227

/-! Arithmetic receipts only: the mathematical high-row support argument
    and recovery of the matrices from the official radicals are separate. -/

private def removeAt : Nat → List Int → List Int
  | _, [] => []
  | 0, _ :: x => x
  | n+1, a :: x => a :: removeAt n x

private def det : Nat → List (List Int) → Int
  | 0, _ => 1
  | Nat.succ _, [] => 0
  | n+1, r :: rs =>
    (r.zipIdx.map (fun (a,j) =>
      (if j % 2 == 0 then a else -a) * det n (rs.map (removeAt j)))).sum

set_option maxRecDepth 100000
set_option maxHeartbeats 0

"""
with pathlib.Path(sys.argv[1]).open('w') as f:
    f.write(start)
    for line in code.splitlines():
        if not line.startswith('DEF'): continue
        head,v=line.split(' VALUE '); a,b=head[4:].split(' MATRIX ')
        M=ast.literal_eval(b)
        f.write(f'theorem {a} : det {len(M)} {M} % 227 = {v} := by decide\n\n')
    f.write('end RKResearch.ERK10StepanovFiveOpeningMod227\n')
