"""Exact number-field reconstructions: no real root or residue-prime pruning."""
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.agca.extensions import MonogenicFiniteExtension
from itertools import combinations
from scalar_geometry import D,k,N,exact_trace
class Tower(MonogenicFiniteExtension):
    def exquo(self,x,y):return x/y
    quo=exquo
    def convert(self,x,base=None):
        if getattr(x,'ext',None)==self:return x
        return super().convert(x,base)
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
def roots_small(f,cap=3):
    K=f.ring.domain
    x=f.ring.gens[0]
    assert f and 0<=f.degree()<=cap
    if f.degree()==0:return
    f=f.monic()
    if f.degree()==1:
        yield K,-f.get((0,),K.zero),lambda y:y
        return
    assert f.degree() in (2,3)
    # A formal generator of each irreducible factor covers every embedding.
    # Explicitly replay the conjugate for quadratic factors.
    ff=f.factor_list()[1]
    for p,e in ff:
        if p.degree()==1:
            yield K,-p.get((0,),K.zero)/p.LC,lambda y:y
        else:
            assert p.degree() in (2,3)
            pp=S.Poly.from_dict(p.monic().to_dict(),S.Symbol(str(x)),domain=K)
            E=Tower(pp)
            emb=lambda a,E=E,K=K:E.convert(a,K)
            z=E.generator
            yield E,z,emb
            if p.degree()==2:yield E,-emb(p.get((1,),K.zero)/p.LC)-z,emb
def interp(R,t,vals):
    out=R.zero
    for j,(a,c) in enumerate(vals):
        z=R(c)
        for i,(b,_v) in enumerate(vals):
            if i!=j:z*= (t-R(b)).exquo(R(a-b))
        out+=z
    return out
def check_fourth(K,R,t,h,d,u,W,L,A,B,r,lam):
    m=1+h
    kap=k(u)
    f0=K.one/2;f1=kap/2;f2=N(u)/(2*D(u))
    Tf=interp(R,t,[(K.one,f0),(K.one+u,f1),(K.one+2*u,f2)])
    T0=Tf.get((1,),K.zero);T1=Tf.get((2,),K.zero)
    J=R.from_dict({(i+1,):q/(i+1) for (i,),q in Tf.items()})
    c4=R(T0+4*T1/3)+(t+R(m-1))*R((-1+2*T1*(kap+1)/3)/kap)
    n4=(Tf-J).compose(t,t+R(m))
    # The six endpoints/singletons already fill the two literal opening
    # triples. Fourth is the unused copy of either endpoint, or a third D.
    sa=value(L,h)/B
    for q,g4 in [(-h,-2*sa),(h,-2*sa/lam)]:
      assert g4
      if g4==K.one/2 and q==-h:return 'repeat D residual'
      if g4==lam/2 and q==h:return 'repeat D residual'
      if g4==r*value(W,q):return 'D uses graph residual'
      if g4*value(c4,q)==value(n4,q):return 'fourth endpoint passes'
    U=R(value(L,d))-t*(R(value(A,d))+R(B)*t)
    rem=gcd(U,t*R(value(c4,d))-R(value(n4,d)))
    if rem.degree()>0:return 'fourth third passes'
    return 'fourth rejects'
def audit(K,h,d,u,v,kind):
    zero,one=K.zero,K.one
    m=1+h
    den=35*h*h-21*m*m
    if not m or not den:return 'field guard'
    ss=(21*m*m*h*h-15*m**4)/den
    a=6*m*m/7;b=3*m**4/35
    sks=(u-h,2*u-h,h-v,h-2*v)
    ds=(-h,h,d)
    if any(a1==b1 for a1,b1 in combinations(sks+ds,2)):return 'clock collision'
    if not all([u,v,k(u),k(v),D(u),D(v),N(u),N(v),3*u-2,3*v-2]):return 'literal arithmetic guard'
    R,t=ring('t',K)
    W=t*t-R(ss) if kind=='even' else t*(t+R(d))
    if kind=='even':assert not d
    else:
      assert d and d*d==ss
    L=t**4-R(a)*t*t+R(b)
    L3=t**3-R(3*m*m/5)*t
    if not all(value(L,q) for q in ds):return 'D Legendre guard'
    Q=L3-R((h*h-3*m*m/5)/value(L,h))*t*L
    P=t*(t-R(h))*(t+R(h)) if kind=='even' else (t-R(d))*(t-R(h))*(t+R(h))
    assert not Q%(P*W)
    assert gcd(Q,L).degree()==0
    ww=[value(W,x) for x in sks]
    if not all(ww):return 'zero singleton graph'
    ru=k(u)/(2*ww[0]);lam=2*ru*ww[2]/k(v)
    assert ru and lam
    assert ru*ww[1]==N(u)/(2*D(u))
    assert ru*ww[3]==lam*N(v)/(2*D(v))
    S4=R.one
    for x in sks:S4*=t-R(x)
    sr=S4%W;lr=L%W
    if kind=='even':assert lr.degree()==0
    # In both shapes this component is known nonzero at a genuine method.
    if not sr.get((0,),zero):return 'nodal zero component'
    H4=lr.get((0,),zero)/sr.get((0,),zero)
    assert H4
    Ch,rem=(L-R(H4)*S4).div(W)
    assert not rem
    Wf=value(W,-h)
    z=1-2*ru*Wf
    if not z:return 'first D on graph'
    B=(4*ru*value(L,h)-2*value(Ch,-h))/(ru*z)
    if not B:return 'zero B graph'
    A=Ch.exquo(R(ru))-R(B*ru)*W
    assert value(L,-h)==(value(A,-h)+B/2)/2
    if value(L,h)!=(lam/2)*(value(A,h)+B*lam/2):return 'terminal D rejects'
    ce,T=exact_trace(K,R,t,P,W,L,Q,m)
    tr=ce/ru+T(A)
    if tr:return 'normalized trace rejects'
    return check_fourth(K,R,t,h,d,u,W,L,A,B,ru,lam)
