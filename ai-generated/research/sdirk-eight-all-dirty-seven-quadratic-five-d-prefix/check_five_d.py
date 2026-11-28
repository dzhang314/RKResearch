"""All projected five-D fibres: genuine reverse singleton and normalized trace."""
import sympy as S
from sympy.polys.rings import ring
from five_d_products import mathcases,x

def main():
  finite=list(mathcases())
  assert len(finite)==14 and not any(q[0][0].startswith('C') for q in finite)
  ns,nr=0,0
  for key,mm,dds,GG,i,j,gdr,gsr,xs,f in finite:
    assert f is not None
    fp=S.Poly.from_dict(f.to_dict(),x,domain=S.QQ)
    assert fp.is_irreducible
    if fp.degree()==1:
        E=S.QQ;u=-fp.nth(0)/fp.nth(1)
        u=E.convert(u)
    else:
        E=S.QQ.algebraic_field((fp,x));u=E.unit
    def ev(v):
        def poly(q):
            return sum((E.convert(s)*u**j for (j,),s in q.items()),E.zero)
        a,b=poly(v.numer),poly(v.denom)
        assert b
        return a/b
    m=ev(mm);h=m-1;ell=2*m
    ds=list(map(ev,dds));G=list(map(ev,GG))
    one,zero=E.one,E.zero
    ga,gs,sigma=map(ev,(gdr,gsr,xs))
    assert sigma not in ds and len(set(ds))==3
    c42=E.convert(S.Rational(6,7))*m*m
    c40=E.convert(S.Rational(3,35))*m**4
    c3=E.convert(S.Rational(3,5))*m*m
    L=lambda t:t**4-t*t*c42+c40
    L3=lambda t:t**3-c3*t
    beta=-2*L(ds[i])/G[i]
    assert beta and beta==-L(ds[j])/(G[j]*ga)
    R,t=ring('t',E)
    LD=L(t)
    mu=(h*h-c3)/L(h)
    assert mu
    Q0=L3(t)-t*LD*mu
    P=R.one
    for d in ds:P*=t-d
    W=Q0.exquo(P).monic()
    assert Q0==-mu*P*W and W.degree()==2
    Ls=L(sigma)
    ws=W.evaluate(t,sigma)
    if not ws:
        ns+=1
        print(key,fp.degree(),'reverse singleton is graph zero')
        continue
    nu=gs/ws
    assert nu
    def ip(ys):
        ans=R.zero
        for i,z in enumerate(ys):
            v=R(z)
            for j,d in enumerate(ds):
                if i!=j:v*=(t-d)/R(ds[i]-d)
            ans+=v
        return ans
    A0=ip([L(d)/g for d,g in zip(ds,G)])
    T=ip(G)
    def inv(f,g):
        a,b,gg=f.gcdex(g)
        assert gg==R.one
        return a%g
    def tr_modW(f):
        r=f%W
        return 2*r.get((0,),zero)-W.get((1,),zero)*r.get((1,),zero)
    dW=W.diff(t);dL=LD.diff(t)
    if W.gcd(dW).degree()==0:
        uc=-tr_modW(dL*inv(LD*dW,W))
        star=False
    else:
        epsilon=-W.get((1,),zero)/2
        le=L(epsilon)
        dl=dL.evaluate(t,epsilon)
        dd=dL.diff(t).evaluate(t,epsilon)
        assert W==(t-epsilon)**2 and le
        uc=(dl/le)**2-dd/le
        star=True
    H3=4*m**6/175
    rema=(inv(Q0,LD**2)*H3)%(LD**2)
    Wi=inv(W,LD**2)
    Li=inv(LD,W)
    def width(f):
        return ((f*rema)%(LD**2)).get((7,),zero)
    ce=2*uc-ell*width(LD*Wi)
    def trace(f):
        un=tr_modW(f*Li)+sum((f.evaluate(t,d)/L(d) for d in ds),zero)
        return 2*un-ell*width(f)
    # H(sigma)=0 and lambda * normalized trace = 0.
    row1=(-nu*ws*(A0.evaluate(t,sigma)+beta*nu*ws),
           Ls+beta*nu*ws*T.evaluate(t,sigma))
    row2=(trace(A0),ce/nu-beta*trace(T))
    ls=[row1,row2]
    piv=next(((a,b) for a,b in ls if a),None)
    if piv is None:
        outcome='inconsistent zero pivot' if any(b for a,b in ls) else 'free scale'
    else:
        lam=-piv[1]/piv[0]
        if any(a*lam+b for a,b in ls):
            outcome='rank mismatch'
        elif not lam:
            outcome='zero scale'
        elif G[i]==lam/2 or G[j]==lam*ga:
            outcome='duplicate physical pair'
        else:
            outcome='survive'
    print(key,fp.degree(), 'repeated W?',star,'rank outcome',outcome,flush=True)
    assert outcome=='rank mismatch'
    nr+=1
  assert (ns,nr)==(5,9)
  print('all shared and distinct endpoint five-D boundary patterns excluded')

if __name__=='__main__':
    main()
