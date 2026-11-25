#!/usr/bin/env python3
"""Render only the finite split dispatch/assembly wiring; verify committed source hashes.
This is a source generator, not a mathematical or kernel checker. No Lean, no downloads.
"""
import argparse
import csv
from hashlib import sha256
import json
from pathlib import Path
import re


def fail(msg):
    raise ValueError(msg)


def render(spec):
    p = spec['order']
    if not isinstance(p, int) or not 3 <= p <= 99:
        fail('unsupported two-digit grade layout')
    render_name, scaffold, witness, positive_name = (spec[k] for k in (
        'render_namespace', 'scaffold_namespace', 'same_data_namespace', 'positive_theorem'))
    if not all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', x) for x in
               (render_name, scaffold, witness, positive_name)):
        fail('expected simple reviewed declaration and namespace identifiers')
    rn = 'RKCert.ReviewedNative.' + render_name
    sn = 'RKCert.ReviewedNative.' + scaffold
    ns = 'RKResearch.Certified.' + render_name
    opened = ('RKResearch.Certified NativeIntegerSpanClearing NativeIntegerAugmentedChecker '
              'NativeIntegerAugmentedShardJoin NativeIntegerBlock4 ' + scaffold + ' ')
    out = {}
    def put(suffix, imports, body, extra=''):
        mod = rn + '.' + suffix
        if mod in out:
            fail('duplicate module ' + mod)
        txt = ('module\n\n' + ''.join('public import ' + x + '\n' for x in imports) +
               '\n@[expose] public section\n\nnamespace ' + ns + '\n\nopen ' + opened + extra +
               '\n\n' + body.rstrip('\n') + '\n\nend ' + ns + '\n')
        out[mod] = txt.encode('utf-8')
    grades = range(2,p)
    vecs = range(1,p)
    suffix = lambda g,k: f'N{g:02}K{k:02}L{g-k:02}'
    # Enumerate oriented pairs. In particular k,l and l,k are independent obligations.
    body = 'def lowerRecord : (k l : ℕ) → Fin (rank k) → Fin (rank l) → Clearing (rank (k+l))\n'
    body += ''.join(f'  | {k}, {g-k}, i, j => lowerTable{suffix(g,k)} i j\n'
                    for g in grades for k in range(1,g))
    body += ('  | _, _, _, _ => unusedClearing\n\ndef lower : LowerPayload where\n'
             '  window := fun k l _ _ _ i _ j _ _ => lowerRecord k l i j')
    put('Payload.Dispatch', [rn + f'.Payload.G{g:02}' for g in grades], body)
    for g in range(2,p+1):
        top = g == p
        owner = f'Top{p:02}' if top else f'LowerG{g:02}'
        leaves = [('Top' if top else 'Lower') + suffix(g,k) for k in range(1,g)]
        stem = f'Top{p:02}' if top else f'G{g:02}'
        args = 'renderOps header' if top else 'renderOps header lower'
        fields = '\n'.join(f'  split{k:02}_{g-k:02} := rendered{suffix(g,k)}' for k in range(1,g))
        put('Assemble.' + stem, [sn + '.' + owner] + [rn + '.Proof.' + a for a in leaves],
            f'theorem rendered{stem} : {owner}Receipts {args} where\n{fields}')
    vi = [sn + '.Vectors'] + [rn + f'.Proof.{k}G{g:02}' for g in vecs for k in ('A','P')]
    vfields = '\n'.join(f'  {field}{g:02} := rendered{k}N{g:02}' for g in vecs
                        for field,k in [('action','A'),('payment','P')])
    put('Assemble.Vectors', vi, 'theorem renderedVectors : VectorReceipts renderOps header where\n' + vfields)
    imports = [sn + '.Assembly', rn + '.Assemble.Vectors', rn + '.Numeric.LeafScales']
    imports.extend(rn + f'.Assemble.G{g:02}' for g in grades)
    imports.append(rn + f'.Assemble.Top{p:02}')
    fields = (f'  scales := p{p}_scales_bool\n  leaf := p{p}_leaf_bool\n  vectors := renderedVectors\n'
              + ''.join(f'  g{g:02} := renderedG{g:02}\n' for g in grades) + f'  top := renderedTop{p:02}')
    put('Assemble.All', imports, 'theorem literalReceipts : Receipts renderOps header lower where\n' + fields)
    put('Positive', [sn + '.FixedPositive', rn + '.Assemble.All'],
        f'theorem {positive_name} : RKResearch.HasOrder {p} A b :=\n  positive_of_shards header lower literalReceipts',
        extra=witness)
    return out


def verify(spec, rows):
    selected = {}
    for r in rows:
        m = r['module']
        if m in selected:
            fail('duplicate manifest module: ' + m)
        selected[m] = r
    files = {}
    for name, data in render(spec).items():
        rel = 'ai-generated/lean/' + name.replace('.', '/') + '.lean'
        row = selected.get(name, {})
        if row.get('repo_path') != rel or row.get('source_sha256') != sha256(data).hexdigest():
            fail('rendered bytes differ from selected manifest: ' + name)
        files[rel] = data
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--emit', type=Path, help='optional NEW directory; no overwrites')
    a = parser.parse_args()
    spec = json.loads(a.profile.read_text(encoding='utf8'))
    with a.manifest.open(encoding='utf8', newline='') as f:
        files = verify(spec, csv.DictReader(f, delimiter='\t'))
    if a.emit is not None:
        a.emit.mkdir(exist_ok=False)
        for rel, data in sorted(files.items()):
            path = a.emit / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open('xb') as f:
                f.write(data)
    print(f'SOURCE-ONLY: {len(files)} wiring sources match manifest. No Lean execution.')


if __name__ == '__main__':
    main()
