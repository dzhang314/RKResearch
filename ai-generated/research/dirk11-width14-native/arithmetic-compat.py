#!/usr/bin/env python3
"""Extract the literal arithmetic/check definitions with no Mathlib import.

As a cross-version check this compiles representative unchanged definition
bodies with the ordinary kernel. The full reviewed theorem also requires
the pinned Mathlib and is a separate build.
"""
from pathlib import Path
import argparse

here=Path(__file__).resolve().parent
pa=argparse.ArgumentParser()
pa.add_argument('output',type=Path)
pa.add_argument('--lean',type=Path,default=here.parent.parent/'lean/RKCert/ReviewedNative')
args=pa.parse_args()
stem='DIRK11Width14Integer'
def body(n):
    return (args.lean/(n+'.lean')).read_text().split('@[expose] public section\n',1)[1]
arith=body('QuadTowerIntReplay').split('section Semantics',1)[0]+'end RKResearch.Certified.QuadTowerIntReplay\n'
core=(body(stem+'Core').split('section Generic',1)[0]
    .replace('open RKResearch FiniteRootedTree Graded QuadTowerIntReplay','open QuadTowerIntReplay')
    .replace('open scoped Matrix BigOperators FiniteRootedTree\n',''))+f'end RKResearch.Certified.{stem}Core\n'
data=body(stem+'Data')
args.output.write_text('import Lean\n\n'+arith+'\n'+core+'\n'+data+'\n'+'''open RKResearch.Certified.DIRK11Width14IntegerCore
open RKResearch.Certified.DIRK11Width14IntegerData
set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem compat_node : checkNode packet = true := by decide +kernel
theorem compat_quadrature : checkScalar packet 10 = true := by decide +kernel
theorem compat_nonaccrual : checkA packet 3 ⟨0,by decide⟩ = true := by decide +kernel
theorem compat_product : checkProduct packet 3 3 ⟨0,by decide⟩ ⟨0,by decide⟩ = true := by decide +kernel
theorem compat_failure : checkFailure packet = true := by decide +kernel
#print axioms compat_failure
''')
