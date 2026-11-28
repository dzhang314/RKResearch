"""Distinct both-D, one extra D versus arithmetic D,S,S; true rank projection."""
from scalar_geometry import shape
from sympy.polys.fields import field
import sympy as S
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from itertools import combinations,product

F,h,d,v=field('h,d,v',S.QQ)
C=MC.get(('h','d','v'),'lex')
hh,dd,vv=C.gens()
m=h+1;den=35*h*h-21*m*m
Th=35*hh*hh*dd*dd-21*(hh+1)**2*(hh*hh+dd*dd)+15*(hh+1)**4
S0=(21*m*m*h*h-15*m**4)/den
L=lambda t:t**4-F(6)*m*m*t*t/7+F(3)*m**4/35
k=lambda t:1+2*t-t*t
D=lambda t:-2+t+4*t*t-t**3
N=lambda t:(1+4*t-4*t*t)*D(t)+4*t*t*(3*t-2)
def copy(p):
    if not p:return C.constant(0)
    lc=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,i)):int(c*lc) for i,c in p.items()})
def strip(p,gs):
    if not p:return p
    for n in gs:
      while (q:=p.gcd(n)).total_degree()>0:
        p,r=divmod(p,q);assert not r
    return p
def cip(x,vs):
    val=F.zero
    for i,(q,z) in enumerate(vs):
        for j,(r,w) in enumerate(vs):
            if i!=j:z=z*(x-r)/(q-r)
        val+=z
    return val
def core(kind,choice,f):
    dd=F.zero if kind=='even' else d
    ds=[-h,h,dd]
    W=(lambda t:t*t-S0) if kind=='even' else (lambda t:t*(t+d))
    extra=h if choice=='reuse' else dd
    gd,sf,gf,gu=shape(h+extra,f);sf-=h
    s2=h-v;s3=h-2*v;ah=L(h)
    wb=dd
    gs=[m,h,den,L(h),L(dd),gd,gf,W(sf),W(s2),W(s3),sf-s2,sf-s3,v,k(v),D(v),N(v),3*v-2]+gu
    gs+=[x-y for x in [sf,s2,s3] for y in ds]
    if kind=='split':gs+=[dd,dd-h,dd+h]
    if not all(gs):return None
    r=gf/W(sf)
    mu=2*r*W(s2);kv=k(v)
    qo=D(v)-v*(v-2)*(3*v-2)
    ratio=D(v)*(2*h+wb-3*v)-(v-2)*(3*v-2)*W(s2)
    assert ratio*v*kv==N(v)*W(s2)-D(v)*kv*W(s3)
    beta=None;data=None
    if choice=='reuse':
      beta=-2*ah/gd
      gs.append(kv*gd-mu/2)
      pts=[(-h,2*mu*ah-beta*kv/2+beta*r*kv*W(-h)),
           (h,-beta*(kv*gd+mu/2)+beta*r*kv*W(h)),
           (sf,mu*L(sf)/gf)]
      f2=2*L(s2)-cip(s2,pts)
      f3=2*D(v)*L(s3)-qo*cip(s3,pts)
      eq=[f2,f3]
      data=pts
    else:
      aa=[(-h,2*kv*mu*ah),(h,2*kv*kv*ah),(dd,kv*mu*L(dd)/gd)]
      bb=[(-h,kv*(r*W(-h)-F.one/2)),(h,kv*r*W(h)-mu/2),
          (dd,kv*(r*W(dd)-gd))]
      aco=[cip(s2,bb), qo*cip(s3,bb),cip(sf,bb)]
      bco=[cip(s2,aa)-2*kv*L(s2),qo*cip(s3,aa)-2*D(v)*kv*L(s3),
           cip(sf,aa)-kv*mu*L(sf)/gf]
      eq=[a*z-b*c for (a,b),(c,z) in combinations(zip(aco,bco),2)]
      data=(aa,bb,aco,bco)
    assert all(gs)
    gi=[copy(a.numer) for a in gs];gden=[copy(a.denom) for a in gs]
    for f0 in [ratio]+eq:
        assert strip(copy(f0.denom),gi+gden).total_degree()==0
    return [strip(copy(z.numer),gi) for z in [ratio]+eq],gi,gs,ratio,data,r,mu,beta,W,ds,sf,s2,s3,gd,gf

def projects():
 for kind,choice,f in product(('even','split'),('reuse','third'),('A2','A3','S')):
    data=core(kind,choice,f)
    if data is None:
        print(kind,choice,f,'literal guard',flush=True)
        continue
    pp,gi,*_=data
    gd=C.constant(0);ds=[]
    for q in pp[1:]:
        if not q:continue
        rr=pp[0].resultant(q,'v')
        if not rr:continue
        if kind=='split':
            rr=strip(rr,[p for p in gi if not p.degrees()[-1]])
            rr=Th.resultant(rr,'d')
            if not rr:continue
        gd=strip(gd.gcd(rr),[p for p in gi if p.degrees()[1:]==(0,0)])
        ds.append(rr.total_degree())
    assert gd
    fac=gd.factor()[1]
    expected= {
     ('even','reuse','A2'):[27,63], ('even','reuse','S'):[18,54],
     ('even','third','A3'):[96,69,93], ('even','third','S'):[78,57,75],
     ('split','reuse','A2'):[70,108], ('split','reuse','S'):[52,90],
     ('split','third','A2'):[210,164,198], ('split','third','A3'):[206,180,194],
     ('split','third','S'):[158,112,146]}
    assert ds==expected[kind,choice,f] and not fac
    print(kind,choice,f,'guarded exact projection degrees',ds,'unit gcd',flush=True)
    yield kind,choice,f,fac,data
if __name__=='__main__':
    assert len(list(projects()))==9
    print('all nine actual reverse-arithmetic branches excluded')
