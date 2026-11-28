#!/usr/bin/env python3
"""Replay the exact old-contact fourth zero-diagonal hinge and predecessor hashes."""
import argparse
from hashlib import sha256
from pathlib import Path
from runpy import run_path
here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--research',type=Path,default=here.parent)
parser.add_argument('--old-core',type=Path)
parser.add_argument('--prime',type=int,action='append')
a=parser.parse_args()
old=a.old_core or a.research/'dirk11-thirteen-invisible-local-slack-old-twin'/'project.py'
ring=a.research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
for path,receipt in ((old,'old-project.sha256'),(ring,'ring.sha256')):
    assert sha256(path.read_bytes()).hexdigest()==(here/receipt).read_text().strip()
core=run_path(str(old))
for p in a.prime or [101]:
    core['ranks'](a.research,p)
