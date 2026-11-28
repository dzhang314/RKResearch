from pathlib import Path
from flint import fmpz_poly,fmpq,fmpq_poly,nmod_poly
import argparse,time
p=argparse.ArgumentParser()
p.add_argument('first',type=Path);p.add_argument('--guards',type=Path,default=Path('frexact'))
p.add_argument('--ledger',type=Path);p.add_argument('--out',type=Path,required=True)
a=p.parse_args();t=time.monotonic()
def log(*x):print(round(time.monotonic()-t,2),*x,flush=True)
def read(cs):
 z=fmpq_poly([fmpq(c)for c in cs]).numer();return z//z.content()if z!=0 else z
def rad(x):
 return x//x.gcd(x.derivative())
def reduction(g,p):
 return nmod_poly([int(x)%p for x in g.coeffs()],p)
fac=set()
files=[(f.stem,read(f.read_text().split()))for f in sorted(a.guards.glob('G*'))]
if a.ledger:
 for ln in a.ledger.read_text().splitlines():
    sr=ln.split();j=next(i for i,x in enumerate(sr)if x[0]=='-'or x[0].isdigit())
    files.append((' '.join(sr[:j]),rad(read(sr[j:]))))
F=read(a.first.read_text().split())
log('first degree',F.degree())
G=fmpz_poly([1])
for tag,h in files:
    if h==0:continue
    for g,_ in h.factor()[1]:
        ID=tuple(map(int,g.coeffs()))
        if ID in fac:continue
        fac.add(ID)
        if F.degree()<g.degree():continue
        # Use modular image only as a proposal for how many copies to test.
        # Every removed factor is independently divided out exactly.
        prime=next(q for q in [103,109,127,137,139,151,179,181] if int(F.leading_coefficient())%q and int(g.leading_coefficient())%q)
        fv,gv=(reduction(x,prime)for x in (F,g))
        n=0
        while (r:=fv%gv)==0:
            fv=fv//gv;n+=1
        if n==0:continue
        zz=F
        m=0
        while n:
            f0,r=divmod(zz,g**n)
            if r==0:
                zz=f0;m+=n
                if zz.degree()==0:break
                # The previous n can at most be repeated only up to
                # original residue exponent (use exact trial anyway).
                if m==n:break
            n//=2
        if m:
            F=zz;G*=g
            log('discarded exact guard',tag,g.degree(),m,'left',F.degree())
# Finish any partial exponent individually (normally valuation tests
# at a good residue prime inflated nothing).
for tag,h in files:
    if h==0:continue
    d=F.gcd(h)
    while d.degree()>0:
        F,r=divmod(F,d)
        assert r==0
        G*=d//d.gcd(G)
        log('extra root support',tag,d.degree(),'left',F.degree())
        d=F.gcd(h)
Fr=rad(F);Gr=rad(G)
Fr=Fr//Fr.content();Gr=Gr//Gr.content()
a.out.write_text(' '.join(map(str,Fr.coeffs()))+'\n')
a.out.with_suffix('.guards').write_text(' '.join(map(str,Gr.coeffs()))+'\n')
log('residual',Fr.degree(),'guard',Gr.degree())
