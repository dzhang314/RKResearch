#!/usr/bin/env python3
"""Same quadratic gates in all four finite alternate old clocks."""
import argparse,hashlib,sys
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('profile',choices=['F1','F2','H3','H5','Fn-loss','m1','mY2','contact'])
ap.add_argument('--research',type=Path,required=True)
ap.add_argument('--p',type=int)
ap.add_argument('--residue-index',type=int,default=0)
opt=ap.parse_args()
name='dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f'
cases={
 'F1':('1','8ad9396ece9684040108275e7dfc224786e6cc0140ee281228c8052e0276fa1c',[]),
 'F2':('2','f9386e78465d38dd12cf4d3c742473159ad05466c4592bc70bfac2bc51957663',[]),
 'H3':('n','eab8a0b05f98e798c7be405b137008f8887004da8fa1284acd294b71526e309e',['H3']),
 'H5':('n','eab8a0b05f98e798c7be405b137008f8887004da8fa1284acd294b71526e309e',['H5']),
}
if opt.profile in cases:
    suffix,digest,case=cases[opt.profile]
    model=opt.research/(name+suffix)/'proof.py'
else:
    model=opt.research/'dirk11-thirteen-invisible-six-alpha-one-beta-zero-finite-contacts'/'proof.py'
    digest='847c63a0dde571940145b62d20bedb5df1b0b00abe7004788ba60b95e60f5261'
    case=[opt.profile]
prime=opt.p or (101 if opt.profile=='contact' else 103)
raw=model.read_bytes()
assert hashlib.sha256(raw).hexdigest()==digest
anchor='tt=T.gen()\n'
data=raw.decode()
assert data.count(anchor)==1
data=data.split(anchor)[0]
assert 'hbq' not in data and 'c_q' not in data
sys.argv=[str(model),*case,'--p',str(prime),'--residue-index',str(opt.residue_index)]
art=Path(__file__).with_name('two-rows.py')
exec(compile(data,str(model),'exec'),globals())
V,zp,zq,den,el,to=v,p0,q0,n,ell,rho
exec(compile(art.read_text(),str(art),'exec'))
Q=five()
def basis(r):
    if r is base:return [base.to(1)]
    return [r.to(x)*r.gen()**i for i in range(r.n)for x in basis(r.low)]
def vect(e):
    if isinstance(e,PE):return [e.f]
    return sum([vect(x)for x in e.cs],[])
bb=basis(S)
dim=len(bb)
def rank(gs):
    piv={}
    for f in gs:
        for x in bb:
            v=vect(f*x)
            for i in range(dim):
                if v[i]==0:continue
                h=v[i]
                if i in piv:
                    d=piv[i]
                    for j in range(i+1,dim):v[j]=(v[j]-h*d[j])%baseMod
                    continue
                g,iv,_=h.xgcd(baseMod)
                assert g==1 and h*iv%baseMod==1
                piv[i]=[None]*(i+1)+[v[j]*iv%baseMod for j in range(i+1,dim)]
                break
    return len(piv)
aa,jj=rank([A]),rank([A,Q])
print(opt.profile,prime,'residue',baseMod,'ranks A/joint/dim',aa,jj,dim,flush=True)
assert jj==dim
