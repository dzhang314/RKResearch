"""Exact one-overlap phase projection: known three D labels and two S fits."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from itertools import combinations,product
F,H,d=field('H,d',S.QQ)
C=MC.get(('H','d'),'lex')
m=(H+2)/2
def K(u):return 1+2*u-u*u
def D(u):return -2+u+4*u*u-u**3
def N(u):return (1+4*u-4*u*u)*D(u)+4*u*u*(3*u-2)
def pair(u,phase):
    if phase=='S':return K(u)/2,K(u)/2,[u,u-1,u-2,K(u)]
    return K(u)/2,N(u)/(2*D(u)),[u,K(u),D(u),N(u),3*u-2]
def lp(y,j):
    b=y-H/2
    return b**3-3*m*m*b/5 if j==3 else b**4-6*m*m*b*b/7+3*m**4/35
def mon(p):
    if not p:return C.constant(0)
    z=lcm(*(int(S.Rational(a).q) for a in p.values()))
    return C.from_dict({tuple(map(int,ix)):int(a*z) for ix,a in p.items()})
def num(f):return mon(f.numer)
def strip(p,gs):
    for q in gs:
        while p and (a:=p.gcd(q)).total_degree()>0:
            p,b=divmod(p,a)
            assert not b
    return p
def interp(x,readings):
    z=F.zero
    for a,h in readings:
        for b,j in readings:
            if a!=b:h*= (x-b)/(a-b)
        z+=h
    return z
def frame(mo,fo,ro):
    q,r=(H,d) if mo=='terminal' else (d,H)
    if fo=='A2':
      e=2*q;fq,fe,fg=pair(q,'A');u=q
    elif fo=='A3':
      e=q/2;fe,fq,fg=pair(e,'A');u=e
    else:
      e=2-q;fq,fe,fg=pair(q,'S');u=q
    if ro=='A2':
      s=2*d-H;gd,gs,rg=pair(H-d,'A')
    elif ro=='A3':
      s=(H+d)/2;gs,gd,rg=pair((H-d)/2,'A')
    else:
      s=2*H-2-d;gd,gs,rg=pair(H-d,'S')
    Ds=[H,d,e]
    gg=[('m',m),('first-departure',u-2)]
    gg += [('front phase',z) for z in fg]+[('rear phase',z) for z in rg]
    zz=list(zip(('0','s','H','d','e'),[F.zero,s]+Ds))
    gg += [('clock '+a+'≠'+b,x-y) for ((a,x),(b,y)) in combinations(zz,2)]
    gg += [('center '+nm,2*x-H) for nm,x in zz[2:]]
    gg += [('opposite '+a+','+b,x+y-H) for ((a,x),(b,y)) in combinations(zz[2:],2)]
    gg += [('Legendre '+nm,lp(x,4)) for nm,x in zz[2:]]
    if fo=='S':gg += [('star first-departure other order',e-2)]
    if any(not z for _,z in gg):return None
    base=[num(z) for _,z in gg]
    assert all(mon(z.denom).total_degree()==0 for _,z in gg)
    tq,tr=(F.one/2,gd) if mo=='terminal' else (gd,F.one/2)
    a=lp(H,3)/lp(H,4)
    b=(lp(d,3)/lp(d,4)-a)/(d-H)
    T,y=ring('y',F.to_domain())
    t=y-T(H/2)
    L3=t**3-T(3*m*m/5)*t
    L4=t**4-T(6*m*m/7)*t*t+T(3*m**4/35)
    Q=L3-(T(a)+T(b)*(y-T(H)))*L4
    M=Q.exquo((y-T(H))*(y-T(d)))
    assert M.degree()==3 and b
    M0=M.get((0,),F.zero);Ms=M.evaluate(y,s)
    ee=M.evaluate(y,e)
    assert ee and M0 and Ms
    gg += [('affine projection slope',b),('first graph value',M0),('rear graph value',Ms)]
    assert all(strip(mon(z.denom),base).total_degree()==0 for _,z in gg)
    beta=-lp(q,4)/(fq*tq)
    aco=[(q,-beta*fq),(r,lp(r,4)/tr),(e,-beta*fe)]
    bco=[(q,-beta*tq),(r,-beta*tr),(e,lp(e,4)/fe)]
    Llam=2*M0*(s-e)*gs;Ulam=-e*Ms
    t0=interp(F.zero,aco)+beta/2
    t1=interp(F.zero,bco)-2*lp(F.zero,4)
    r0=gs*interp(s,aco)-lp(s,4)
    r1=gs*interp(s,bco)+beta*gs*gs
    f0=Llam*t0+Ulam*t1
    f1=Llam*r0+Ulam*r1
    named=[(nm,num(g)) for nm,g in gg]+[('proved unit denominator',mon(g.denom)) for nm,g in gg]
    gi=[z for _,z in named]
    for f in [ee,f0,f1]:assert strip(mon(f.denom),gi).total_degree()==0
    E,X,Y=[strip(num(f),gi) for f in [ee,f0,f1]]
    return named,E,X,Y
EXPECTED={
 ('terminal','A2','A2'):[(8,1)],('terminal','A2','A3'):[(4,1),(8,1)],
 ('terminal','A2','S'):[(9,1)], ('terminal','S','A2'):[(8,1)],
 ('terminal','S','A3'):[(8,1)], ('terminal','S','S'):[(4,1),(8,1)],
 ('extra','A2','A2'):[(2,2),(4,1)], ('extra','A2','A3'):[(2,1),(4,1),(4,1),(4,1)],
 ('extra','A2','S'):[(2,1),(4,1),(9,1)], ('extra','A3','A2'):[(2,1),(4,1),(4,1),(4,1)],
 ('extra','A3','A3'):[(2,2),(4,1),(4,1)], ('extra','A3','S'):[(2,1),(4,1),(9,1)],
 ('extra','S','A2'):[(1,1),(2,1),(4,1),(8,1)], ('extra','S','A3'):[(1,2),(2,1),(4,1),(8,1)],
 ('extra','S','S'):[(1,1),(2,2),(4,1),(4,1)],
}
def project():
  visited=set()
  losses=set()
  for mo,fo,ro in product(('terminal','extra'),('A2','A3','S'),('A2','A3','S')):
    data=frame(mo,fo,ro)
    if data is None:
      losses.add((mo,fo,ro))
      print(mo,fo,ro,'impossible literal chart',flush=True);continue
    named,E,X,Y=data
    gi=[z for _,z in named]
    assert E and (X or Y)
    hp=[p for p in gi if p and p.degrees()[1]==0]
    outs=[]
    for B in [X,Y]:
      rs=E.resultant(B,'d');outs.append(strip(rs,hp))
    g=outs[0].gcd(outs[1])
    ff=g.factor()[1] if g else []
    ds=[a.total_degree() for a in [E,X,Y]+outs]
    print(mo,fo,ro,'projection degrees',ds,'gcd factors',[(f.total_degree(),e) for f,e in ff],flush=True)
    assert g and sorted((p.total_degree(),a) for p,a in ff)==EXPECTED[mo,fo,ro]
    assert all(outs) and E.total_degree()==9
    visited.add((mo,fo,ro))
    yield mo,fo,ro,ff,data
  assert visited==set(EXPECTED)
  assert losses=={('terminal','A3',r) for r in ('A2','A3','S')}
if __name__=='__main__':run=list(project())
