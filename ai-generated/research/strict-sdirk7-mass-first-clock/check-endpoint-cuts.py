#!/usr/bin/env python3
from check_fibers import *

def bezout(H,G,AN,AD,CN,CD):
 return sum((H[i]*G[j]-G[i]*H[j])*sum(AN**(i-1-k)*AD**(3-i+k)*CN**(j+k)*CD**(2-j-k)
    for k in range(i-j)) for i in range(1,4) for j in range(i))

def transfer(g,C,xs):
    rd,ed=g.degrees()[1:]
    t,yn,yd,en,edn=xs
    powlist=lambda q,k:[q**i for i in range(k+1)]
    U=powlist(t,g.degrees()[0])
    Rs,Rd,Es,Ed=powlist(yn,rd),powlist(yd,rd),powlist(en,ed),powlist(edn,ed)
    return sum((int(v)*U[i]*Rs[j]*Rd[rd-j]*Es[k]*Ed[ed-k] for (i,j,k),v in g.to_dict().items()),C.constant(0))

def qZero():
    Cs=fmpz_mpoly_ctx.get(('u','r','e'),'lex');u,r,e=Cs.gens()
    F,_,(N,D),H,G,den=op(u,r,e)
    P=bezout(H,G,-1,1,r*N-D,D)
    d=[w for i,w in enumerate(den) if i not in (14,19)]+[1+e,r*N]
    C=fmpz_mpoly_ctx.get(('u','x'),'lex');u,x=C.gens()
    def push(g):
        return transfer(g,C,[u,4*(x-1),x*(x-2),2-3*x,x-2])
    ff,pp=map(push,[F,P])
    dd=[x,x-1,x-2]+list(map(push,d))
    Fs,Ps=(sat(w,dd) for w in (ff,pp))
    R=sat(Fs.resultant(Ps,0),dd[:3])
    print('q a0 operands',Fs.degrees(),Ps.degrees(),'projection',R.degrees(),flush=True)
    rec=univ_roots(univ(R,1))
    assert sorted(rec)==[(9,2,11,[]),(27,2,13,[]),(36,1,11,[]),(84,1,37,[])]
    print('q a0 factors',rec,flush=True)

def h2cZ(u0=None):
    if u0 is None:
      C=fmpz_mpoly_ctx.get(('u','r','e'),'lex');u,r,e=C.gens()
      ell=2
    else:
      C=fmpz_mpoly_ctx.get(('r','e'),'lex');r,e=C.gens();u=u0
      ell=1
    F,_,(N,D),H,G,den=op(u,r,e)
    x=1-e
    ma=x*x-4*x*r+2*r*r
    h=x**3-6*x*x*r+9*x*r*r-3*r**3
    AD=3*ma; AN=(1-r)*AD-2*h
    h2den=[asvalue(C,w) for i,w in enumerate(den) if i not in (14,19)]
    h2den.extend([AD,AN-AD,AN-e*AD])
    P=bezout(H,G,AN,AD,1,1)
    Qh=r*N-2*D
    Fa,Pa,Ca=(sat(w,h2den) for w in (F,P,Qh))
    R0=Fa.resultant(Ca,ell)
    R1=Fa.resultant(Pa,ell)
    print('h2 c=z',u0,'projected (op,c)',R0.degrees(),'(op,first)',R1.degrees(),flush=True)
    bdr=[p for p in h2den if p.degrees()[ell]==0]
    Gd=sat(R0.gcd(R1),bdr)
    print('common projection',Gd.degrees(),flush=True)
    if u0 is not None:
      if Gd.total_degree()>0:print('r factors',univ_roots(univ(Gd)),flush=True)
    else:
      assert Gd.total_degree()==0, Gd.factor()

if __name__=='__main__':
   a=argparse.ArgumentParser()
   a.add_argument('--q',action='store_true')
   a.add_argument('--h2',action='store_true')
   b=a.parse_args()
   if b.q:qZero()
   if b.h2:
      h2cZ(5)
      h2cZ()
