"""Exact exceptional fields; no half-amplitude branch is divided out."""
from sympy.polys.rings import ring
import sympy as S
from projection import project,NN,DD,d as lit_d
def K_h(f):
    X=S.Symbol('h')
    p=S.Poly.from_dict({(int(ix[0]),):int(c) for ix,c in f.to_dict().items()},X,domain=S.QQ)
    assert p.is_irreducible
    if p.degree()==1:return S.QQ,S.QQ.convert(-p.nth(0)/p.nth(1))
    K=S.QQ.algebraic_field((p,X))
    return K,K.unit
def value(p,x):
    K=p.ring.domain
    acc=K.zero
    for c in p.to_dense():acc=acc*x+c
    return acc
def gcd(p,q):
    while q:p,q=q,p%q
    return p.monic() if p else p
def strip(p,gs):
    for g in gs:
        while p and (q:=gcd(p,g)).degree()>0:p=p.exquo(q)
    return p
def specialize(f,R,xs):
    # None means leave one coordinate as R's variable.
    K=R.domain
    powers={}
    for i,a in enumerate(xs):
       if a is not None:powers[i]=[a**j if j else K.one for j in range(f.degrees()[i]+1)]
    terms={}
    for ix,c in f.to_dict().items():
      g=K.convert(int(c));m=0
      for i,e in enumerate(ix):
        if xs[i] is None:m+=int(e)
        else:g*=powers[i][e]
      terms[(m,)]=terms.get((m,),K.zero)+g
    return R.from_dict({i:c for i,c in terms.items() if c})

def regular():
 seen=set();fibres=set()
 for reuse,fo,gf,gg,rr,d in project():
    seen.add((reuse,fo))
    for f,n in gf:
        K,H=K_h(f);R,t=ring('d',K)
        sp=lambda p:specialize(p,R,[H,None])
        rs=list(map(sp,rr))
        raw=gcd(gcd(rs[0],rs[1]),rs[2])
        assert raw
        th=strip(raw,[sp(z) for z in gg])
        print(fo,'exact H degree',f.total_degree(),'raw/guarded d degree',raw.degree(),th.degree(),flush=True)
        assert not reuse and fo=='A2' and n==1
        assert raw.degree()==1 and f.total_degree() in (1,3)
        v=-raw.get((0,),K.zero)
        if f.total_degree()==1:
            assert H==3 and v==2
            print('first-departure clock: H=3,d=2',flush=True)
        else:
            assert v==H-1 and v**3-3*v*v+1==K.zero
            print('specialization lies on the independently checked half-amplitude branch',flush=True)
        fibres.add(f.total_degree())
        assert th.degree()==0
 assert seen=={(z,h) for z in (True,False) for h in ('A2','A3','S')}
 assert fibres=={1,3}
def singular():
    z=lit_d
    assert NN(z)-DD(z)==4*z*(z-2)*(z**3-3*z*z+1)
    x=S.Symbol('d')
    f=S.Poly(x**3-3*x*x+1,x,domain=S.QQ)
    assert f.is_irreducible
    K=S.QQ.algebraic_field((f,x));d=K.unit
    H=d+1;m=(H+2)/2
    assert d and H and m and H-2
    U,y=ring('y',K)
    t=y-U(H/2)
    L3=t**3-U(3*m*m/5)*t
    L4=t**4-U(6*m*m/7)*t*t+U(3*m**4/35)
    a=L3.evaluate(y,H)/L4.evaluate(y,H)
    b=(L3.evaluate(y,d)/L4.evaluate(y,d)-a)/(d-H)
    assert b
    M=(L3-(U(a)+U(b)*(y-U(H)))*L4).exquo((y-U(H))*(y-U(d)))
    e=-M.get((2,),K.zero)/M.LC-2*d
    value=M.evaluate(y,e)
    print('half-amplitude cubic Vieta branch: M(e) nonzero',bool(value),flush=True)
    assert value
if __name__=='__main__':regular();singular()
