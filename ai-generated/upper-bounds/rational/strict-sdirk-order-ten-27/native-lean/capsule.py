#!/usr/bin/env python3
"""Optional single-copy transport of the 1,358 rendered UTF-8 Lean sources. No Lean or Git."""
import argparse
import gzip
from hashlib import sha256
import io
from pathlib import Path
import re
import tarfile
from check_cut import L, MOD, P, U, hashed, local, need, table


def selection(manifest, digest):
    rows=table(hashed(manifest,digest)); chosen={}; seen=set()
    need(len(rows)==1386,'not the selected 1,386-provider spine')
    for r in rows:
        m=r['module']; name=r['repo_path']; h=r['source_sha256']
        need(MOD.fullmatch(m) and m not in seen and name==L+m.replace('.','/')+'.lean' and re.fullmatch(r'[0-9a-f]{64}',h),'noncanonical/duplicate source '+str(m))
        seen.add(m)
        if m.startswith(P) or m==U: chosen[name]=h
    need(len(chosen)==1358,'wrong number of rendered sources')
    return chosen


def canonical(files):
    buf=io.BytesIO()
    with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as t:
        for n,b in sorted(files.items()):
            info=tarfile.TarInfo(n); info.size=len(b); info.mode=0o644
            info.uid=info.gid=info.mtime=0; info.uname=info.gname=''
            t.addfile(info,io.BytesIO(b))
    return buf.getvalue()


def compress(raw):
    buf=io.BytesIO()
    with gzip.GzipFile(filename='',fileobj=buf,mode='wb',compresslevel=9,mtime=0) as f: f.write(raw)
    return buf.getvalue()


def unpack(blob, chosen):
    # Transport caps are for decoding untrusted archives, not computational search limits.
    with gzip.GzipFile(fileobj=io.BytesIO(blob)) as z: raw=z.read(64*1024*1024+1)
    need(len(raw)<=64*1024*1024,'archive exceeds transport size limit')
    files={}
    with tarfile.open(fileobj=io.BytesIO(raw),mode='r:') as t:
        for obj in t:
            n=obj.name
            need(obj.type==tarfile.REGTYPE and n in chosen and n not in files and 0<=obj.size<=4*1024*1024,'extra/duplicate/nonregular or oversized entry '+n)
            b=t.extractfile(obj).read(); need(len(b)==obj.size and sha256(b).hexdigest()==chosen[n],'wrong bytes '+n)
            files[n]=b
    need(files.keys()==chosen.keys(),'missing source file')
    need(canonical(files)==raw,'not canonical USTAR (order, fields, padding or trailing data)')
    return files


def install(root, files):
    root=root.resolve(); need(root.is_dir(),'repository not found')
    targets={name:local(root,name) for name in files}
    for n,p in targets.items():
        need(not p.exists(),'would overwrite existing source '+n)
        for parent in p.parents:
            if parent==root: break
            need(not parent.exists() or parent.is_dir(),'non-directory source parent: '+str(parent))
    for n,p in targets.items():
        p.parent.mkdir(exist_ok=True,parents=True)
        with p.open('xb') as f: f.write(files[n])


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('action',choices=['pack','verify','materialize'])
    p.add_argument('--repo',default=Path('.'),type=Path); p.add_argument('--manifest',required=True,type=Path)
    p.add_argument('--manifest-sha256',required=True); p.add_argument('--bundle',required=True,type=Path)
    p.add_argument('--bundle-sha256',help='pinned release blob SHA (required except for pack)')
    a=p.parse_args(); chosen=selection(a.manifest,a.manifest_sha256); root=a.repo.resolve()
    if a.action=='pack':
        files={n:hashed(local(root,n),h) for n,h in chosen.items()}; raw=canonical(files); blob=compress(raw)
        need(unpack(blob,chosen)==files,'internal roundtrip failure')
        with a.bundle.open('xb') as f: f.write(blob)
    else:
        need(a.bundle_sha256 and a.bundle.stat().st_size<=64*1024*1024,'required archive digest / transport size')
        blob=hashed(a.bundle,a.bundle_sha256); files=unpack(blob,chosen)
        if a.action=='materialize': install(root,files)
    print(f'{a.action}: {len(files)} hash-bound source files, {len(blob)} compressed bytes, SHA256 {sha256(blob).hexdigest()}. No Lean execution.')


if __name__=='__main__': main()
