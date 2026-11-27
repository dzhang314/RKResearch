"""Stage, without changing its arithmetic, the archived directed tableau reconstruction."""
from pathlib import Path
import re,sys

here=Path(__file__).resolve().parent
p=here.parents[1]/'upper-bounds'/'real-algebraic'/'sdirk_p15_34_genuine_nonlinear_gram_target_and_double_literal_merge_20261123_replay.md'
if len(sys.argv)>2:p=Path(sys.argv[2])
js,=re.findall(r'\x60\x60\x60(?:js|javascript)\n(.*?)\n\x60\x60\x60',p.read_text(),re.S)
prefix=js[:js.rindex('let level=typeof process')]
assert 'answer=final34(mesh,low,fwd)' in prefix
prefix+="""
require('fs').writeFileSync('actual34.json',JSON.stringify(
  {precision:B,A:answer.A,b:answer.b},(_k,v)=>typeof v==='bigint'?v.toString():v));
console.log('exported actual enclosed tableau');
"""
Path(sys.argv[1]).write_text(prefix)
