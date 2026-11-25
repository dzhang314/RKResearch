#!/usr/bin/env python3
"""Source-only guard for a materialized public p10 cut. Never calls Lean or Lake."""
import argparse
import csv
from hashlib import sha256
import io
import json
from pathlib import Path
import re

R = 'RKCert.ReviewedNative.'
W = 'RationalStrictSDIRKTwentySevenStageTen'
U = R + W + 'Upper'
P = R + 'P10AugmentedRender.'
A = 'AuditReviewed' + W
L = 'ai-generated/lean/'
M = 'ai-generated/upper-bounds/rational/strict-sdirk-order-ten-27/'
MATHLIB = 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'
EXISTING_SHA = '1e6881ca4d0233b2800174317199e05e2fa4938868fafea720c8cdf633cceb6f'
# The original three stock audit sources must not be rewritten. The tiny fourth is supplemental.
AUDITS = {A+'Data':'41be9f97bbc8d47ccf4c65bf3d04aa35ac447ed7de913ff05f7077da37b6a57a',
          A+'Tall':'f33138ddf85eb7c76c863d2ff92e78e260a1e5b23963a9620337b699b726156b',
          A+'Upper':'a2a6228d190794d30bddda1da8819f58281808cc0f4800bae3b832d9844d8752',
          A+'AugmentedPositive':'2d362c3ac243815b22323965bd7bed2369a13d10176b536171b22c3c47bb2b74'}
IDENTITIES = {R+W+'Data':'fa86709fb7a2da2ce4adad47bbb909c6d57068bd60aa599d5703a4ca8e81e8ed',
              R+W+'Tall':'fd92da420fb205e3abc0576dd7027b8e45d894b34261d9872d0bd848de4efdbe',
              R+'P10AugmentedScaffold.Shape':'7eb8f53bd15685a08c18eeb234a2bd9c2d6b21c784040fa2a9120af62ae0e0fb',
              P+'Payload.Dispatch':'2908a159e8eedf749ed42168e0bc80784527f5197285e43d7801869404d67c77',
              P+'Assemble.All':'a7364a04a86165c678e3df5c3b8fe4a1ca81773f59b997b930e7b47f4efedf48',
              P+'Positive':'7a7fdbd2dcd1afcb2edde65f4f69616c77d60c53ea86597e36726acb6ad8f883',
              U:'de7da22196b016d95f9ca0f1467a57dccf5ea1ad974d7290aaf599b48b4f8c70'}
PINS = {L+'lean-toolchain':'582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a',
        L+'lakefile.toml':'56464e62439bcadda900f13fc3b7de178f8ce7f7fcdfea70aa17605015ca512c',
        L+'lake-manifest.json':'207e593bad22fa516ec10372ae95145ce011ab3ac61f7256dc0b8a1c4b55d820',
        'lakefile.lean':'03448a8d0b91e26cfe77f9361d611f3f6161d42e15b9d17071a450f3a79cf363',
        'lake-manifest.json':'71658e0b20ce36f4211f427f43dccee32d05a6583fbb5db3714ba46e25e5be43',
        M+'tableau.json':'eb0075a13713d9bfb4249391d7d951693c172426ed891b924b2b5c81c0692081'}
MOD = re.compile(r'(?:[A-Za-z][A-Za-z0-9_]*\.)*[A-Za-z][A-Za-z0-9_]*')
SOURCE_IMPORT = re.compile(r'(?:(?:public|private) )?import (' + MOD.pattern + ')')


def need(cond, msg):
    if not cond:
        raise ValueError(msg)


def hashed(path, h):
    need(re.fullmatch(r'[0-9a-f]{64}', h), 'invalid SHA256: '+str(h))
    data = path.read_bytes()
    need(sha256(data).hexdigest() == h, 'source digest mismatch: '+str(path))
    return data


def local(root, rel):
    p = Path(rel)
    need(not p.is_absolute() and all(x not in ('.','..','') for x in rel.split('/')), 'nonrelative source '+rel)
    q = root/p
    need(q.resolve() == q, 'noncanonical/symlinked source path: '+rel)
    return q


def imports(data):
    # Restricted grammar used by this pinned generated family, not a general Lean parser.
    out = []
    for ln in data.decode('utf-8').splitlines():
        if re.match(r'^\s*(?:(?:public|private|meta|all)\s+)*import\b', ln):
            mi = SOURCE_IMPORT.fullmatch(ln.rstrip())
            need(mi is not None, 'unrecognized source import: '+ln)
            out.append(mi[1])
    return out


def lint_source(data):
    # Lexical tripwire in addition to immutable-source review and the real kernel axiom query.
    # The generated subset has no custom lexers; true typed audits remain mandatory.
    s=data.decode('utf-8'); out=[]; i=0; depth=0; string=False
    while i < len(s):
        c=s[i]
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2; continue
            if s.startswith('-/',i): depth-=1; i+=2; continue
            if c=='\n': out.append('\n')
            i+=1; continue
        if string:
            if c=='\\': i+=2; continue
            if c=='"': string=False
            i+=1; continue
        if s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j; continue
        if s.startswith('/-',i): depth=1; i+=2; out.append(' '); continue
        if c=='"': string=True; i+=1; out.append(' '); continue
        out.append(c); i+=1
    need(not depth and not string,'unclosed lexical region in reviewed subset')
    tokens=r'\b(sorryAx|sorry|admit|native_decide|ofReduceBool|trustCompiler|implemented_by|extern|unsafe|axiom|constant)\b'
    found=re.search(tokens,''.join(out)); need(found is None,'unreviewed trust/placeholder token: '+(found[1] if found else ''))


def table(data):
    return list(csv.DictReader(io.StringIO(data.decode('utf-8')), delimiter='\t'))


def check(repo, manifest, manifest_digest, base_map):
    root = repo.resolve()
    for rel,h in PINS.items():
        data = hashed(local(root,rel), h)
        if rel.endswith('lake-manifest.json'):
            need(any(p.get('name')=='mathlib' and p.get('rev')==MATHLIB for p in json.loads(data)['packages']), 'Mathlib revision')
    for name,h in AUDITS.items():
        hashed(local(root,L+name+'.lean'), h)
    rows = table(hashed(manifest, manifest_digest))
    existing = table(hashed(base_map, EXISTING_SHA))
    avail, external, deps, selected = set(), set(), {}, {}
    for row in existing:
        m = row['module']
        need(MOD.fullmatch(m) and m not in avail|external, 'invalid/repeated existing name '+m)
        if row['kind'] == 'existing-base':
            rel = (L if m.startswith('RKCert.') else '') + m.replace('.','/') + '.lean'
            need(row['repo_path_or_revision']==rel, 'invalid base path '+m)
            deps[m] = imports(hashed(local(root,rel), row['sha256']))
            avail.add(m)
        else:
            need(row['kind']=='toolchain/package' and row['repo_path_or_revision']=='leanprover/lean4:v4.36.0 / mathlib '+MATHLIB, 'invalid external dependency '+m)
            external.add(m)
    need(len(rows)==1386, 'not the reviewed 1386-provider cut; refreeze any measured graph change')
    for i,row in enumerate(rows,1):
        m = row['module']
        need(MOD.fullmatch(m) and m.startswith(R) and m not in (avail|external), 'invalid/colliding module '+m)
        rel = L + m.replace('.','/') + '.lean'
        need(row['repo_path']==rel and row['order']==str(i), 'invalid path/order for '+m)
        if m in IDENTITIES:
            need(IDENTITIES[m]==row['source_sha256'], 'anchor requires a new measured review: '+m)
        data=hashed(local(root,rel), row['source_sha256']); lint_source(data)
        ds=imports(data)
        need(ds==row['actual_direct_imports'].split(','), 'wrong actual imports at '+m)
        need(set(ds) <= avail|external, 'missing source/topological prerequisite '+m)
        deps[m] = ds
        avail.add(m)
        selected[m] = row['source_sha256']
    seen = set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        if m in external: return
        need(m in deps, 'unselected provider '+m)
        for d in deps[m]: visit(d)
    visit(U)
    need(seen==avail|external and set(IDENTITIES)<=set(selected), 'unreachable/incomplete whole graph')
    return {'source_status':'SOURCE_BYTES_AND_GRAPH_ONLY', 'selected_sha256':manifest_digest,
            'providers':len(rows), 'existing_project_providers':len(avail)-len(rows),
            'external_import_roots':len(external), 'stock_audits':3,'supplementary_audit':1}


def args(p):
    p.add_argument('--repo', default=Path('.'), type=Path, help='RKResearch repository root')
    p.add_argument('--manifest', type=Path, required=True, help='final selected repository-relative provider ledger')
    p.add_argument('--manifest-sha256', required=True, help='reviewed selection digest, not a self-computed substitute')
    p.add_argument('--existing', type=Path, required=True, help='pinned existing-providers.tsv')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__); args(parser); a=parser.parse_args()
    print(json.dumps(check(a.repo,a.manifest,a.manifest_sha256,a.existing),indent=2))
