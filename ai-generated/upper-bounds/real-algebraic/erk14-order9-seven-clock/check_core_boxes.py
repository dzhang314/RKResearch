#!/usr/bin/env python3
import re
from pathlib import Path
from cert import XL,XU,roots,Box,bracket_at
core=Path(__file__).parent/'../../../lean/RKCert/Research/ERK149SevenClockBracket.lean'
put={'whole':Box(XL,XU),'lower':Box(XL),'upper':Box(XU)}
for j,r in enumerate(roots):
    put['global'+str(j)]=Box(*r)
    put['lo'+str(j)]=bracket_at(XL,r)
    put['hi'+str(j)]=bracket_at(XU,r)
actual={x:(int(l),int(h)) for x,l,h in re.findall(
    r'^def (\w+) : Box := ⟨(\d+), (\d+), true⟩$',core.read_text(),re.M)}
assert actual=={k:(a.l,a.h) for k,a in put.items()}
print('all 12 Lean interval seeds equal the independently generated Python dyadic boxes')
