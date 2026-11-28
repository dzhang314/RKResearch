"""Both distinct D endpoints, one extra D each; non-mutual-reuse patterns."""
from projection_scalars import F,h,d,m,L,k,D,N,delta,S0,Th,C,integer,strip,X
import sympy as S
from itertools import combinations_with_replacement,product

def shape(y,mode):
    if mode=='A2':
        u=y
        return k(u)/2,2*y,N(u)/(2*D(u)),[u,k(u),D(u),N(u),3*u-2]
    if mode=='A3':
        u=y/2
        return N(u)/(2*D(u)),u,k(u)/2,[u,k(u),D(u),N(u),3*u-2]
    return k(y)/2,2-y,k(y)/2,[y,y-1,y-2,k(y)]
def ip(x,vs):
    zz=F.zero
    for i,(t,c) in enumerate(vs):
        for j,(u,s) in enumerate(vs):
            if i!=j:c=c*(x-u)/(t-u)
        zz+=c
    return zz

def structure(kind,patt,f,r):
    if kind=='even':
        dd=F.zero
        W=lambda t:t*t-S0
    else:
        dd=d
        W=lambda t:t*(t+d)
    ff=dd if patt=='match' else h
    gf,sf,gfS,g=shape(h+ff,f)
    gr,sr,grS,q=shape(h-dd,r)
    sf-=h;sr=h-sr
    ds=[-h,h,dd]
    if not W(sf) or not W(sr):return None
    rg=gfS/W(sf)
    lam=rg*W(sr)/grS
    gs=[m,h,delta,L(h),L(dd),gf,gr,gfS,grS,lam,sf-sr,W(sf),W(sr)]+g+q+[a-y for a in [sf,sr] for y in ds]
    if kind=='split':gs+=[dd,dd-h,dd+h]
    if patt=='match':
        beta=-L(dd)/(gf*gr)
        gs.append(gf-lam*gr)
        A0=2*lam*L(h)-beta/2
        Ah=2*L(h)-beta*lam/2
        Ad=-beta*(gf+lam*gr)
    else:
        beta=-2*L(h)/gf
        gs.append(gf-lam/2)
        A0=2*lam*L(h)-beta/2
        Ah=-beta*(gf+lam/2)
        Ad=L(dd)/gr-beta*lam*gr
    if not all(gs):
        return None
    assert beta
    cs=[(y,a+beta*rg*W(y)) for y,a in zip(ds,[A0,Ah,Ad])]
    f0=lam*L(sf)-gfS*ip(sf,cs)
    f1=L(sr)-grS*ip(sr,cs)
    G=[integer(z.numer) for z in gs]
    H=[integer(z.denom) for z in gs]
    for f in [f0,f1]:
        assert strip(integer(f.denom),G+H).total_degree()==0
    return tuple(strip(integer(z.numer),G) for z in [f0,f1]),G,gs,cs,ds,rg,lam,beta,W,sf,sr,gfS,grS

def cases():
  for patt,kind in product(('match','one-reuse'),('even','split')):
    pp=('A2','A3','S')
    ph=combinations_with_replacement(pp,2) if patt=='match' else product(pp,pp)
    for f,r in ph:
        ans=structure(kind,patt,f,r)
        if ans is None:
            print(patt,kind,f,r,'literal guard',flush=True)
            continue
        (a,b),guards,*_=ans
        if kind=='split':
            g=Th.resultant(a,'d').gcd(Th.resultant(b,'d'))
        else:g=a.gcd(b)
        assert g
        g=strip(g,[z for z in guards if not z.degrees()[1]])
        fac=g.factor()[1]
        print(patt,kind,f,r,'guarded factor degrees',[(p.total_degree(),i) for p,i in fac],flush=True)
        yield patt,kind,f,r,fac,ans
if __name__=='__main__':list(cases())
