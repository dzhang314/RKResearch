"""Fixed good-reduction certificate, degree-60 split projection."""
import split_projection as S
from flint import nmod_poly as P
from itertools import product

def specialize(f,p,vals,i=None):
    cs=[0]*(1 if i is None else f.degrees()[i]+1)
    for ix,a in f.to_dict().items():
        z=int(a)
        for j,c in enumerate(vals):
            if j!=i and ix[j]:z=z*pow(c,ix[j],p)%p
        cs[ix[i] if i is not None else 0]+=z
    return P(cs,p) if i is not None else cs[0]%p
def check(p,h,ps):
    K=lambda x:x%p
    def I(x):
        x=K(x)
        if not x:raise ZeroDivisionError()
        return pow(x,-1,p)
    half=I(2)
    m=K(h+1);l0=K(3*m**4*I(35));l2=K(6*m*m*I(7));l4=lambda t:K(t**4-l2*t*t+l0)
    pth,pf,pb,pe=ps
    try:
      if not K(m*h*(35*h*h-21*m*m)*l4(h)):return None
      q=specialize(pth,p,[h,None,0,0],1)
      if q.degree()!=2 or sum(j for _,j in q.roots())!=2:return None
      qds=q.roots()
      det=[]
      for d,mul in qds:
        d=int(d)
        if not K(d*(d-h)*(d+h)*l4(d)):return None
        rf=specialize(pf,p,[h,d,None,0],2)
        rr=specialize(pb,p,[h,d,0,None],3)
        if any(q.degree()!=3 or sum(j for _,j in q.roots())!=3 for q in [rf,rr]):return None
        for (u,_),(v,_) in product(rf.roots(),rr.roots()):
            u=int(u);v=int(v)
            if specialize(pe,p,[h,d,u,v]):continue
            D=lambda x:K(-2+x+4*x*x-x**3)
            k=lambda x:K(1+2*x-x*x)
            N=lambda x:K((1+4*x-4*x*x)*D(x)+4*x*x*(3*x-2))
            W=lambda x:K(x*(x+d))
            ts=[K(u-h),K(2*u-h),K(h-v),K(h-2*v)]
            if len(set(ts+[K(-h),h,d]))!=7:return None
            if not all(K(x*k(x)*D(x)*N(x)*(3*x-2)) for x in [u,v]):return None
            if not all(W(x) for x in ts):return None
            r=K(k(u)*half*I(W(ts[0])))
            lam=K(2*r*W(ts[2])*I(k(v)))
            H4=K(l0*I(ts[0]*ts[1]*ts[2]*ts[3]))
            X=P([0,1],p)
            H=P([H4],p)
            for x in ts:H*=X-x
            L=X**4-l2*X*X+l0
            CW,re=divmod(L-H,X*(X+d))
            assert not re
            B=K((4*r*l4(h)-2*int(CW(K(-h))))*I(r*(1-2*r*W(-h))))
            A=CW*I(r)-K(B*r)*X*(X+d)
            fail=K(l4(h) - lam*half*(int(A(h))+B*lam*half))
            if not fail:return None
            det.append((d,u,v,fail))
      return det
    except ZeroDivisionError:
      return None

def run():
    ff,ps,_,_=S.pi()
    [(f,e)]=[(f,e) for f,e in ff if f.total_degree()==60]
    assert e==2
    x=S.S.Symbol('h')
    g=S.S.Poly.from_dict({(i[0],):int(c) for i,c in f.to_dict().items()},x,domain=S.S.QQ)
    assert g.is_irreducible
    p,h=43,33
    assert all(p%d for d in range(2,1+int(p**0.5)))
    px=specialize(f,p,[None,0,0,0],0)
    assert px.degree()==60 and px(h)==0 and px.derivative()(h)!=0
    out=check(p,h,ps)
    assert sorted(out)==[(14,18,22,29),(29,22,18,23)],out
    print('fixed simple reduction',p,h,sorted(out),flush=True)
if __name__=='__main__':run()
