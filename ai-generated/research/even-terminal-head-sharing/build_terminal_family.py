"""Rebuild the even preparatory and all-head-merged terminal series.

The input is the unchanged 22-stage order-ten preparation from build_even12.py.
The higher computation uses only exact scalar/matrix identities and chronological
row copies. No enumeration of high-order trees or approximation is used.
"""
from __future__ import annotations
from pathlib import Path
from itertools import combinations
import argparse,json,sys,time
import sympy as S
from build_even12 import integral,val,save, R,M,X
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
class Seed:
 def __init__(self,A,b,p,head,pure):
    self.A=A;self.b=b;self.p=p;self.head=head;self.pure=pure
    self.c=A*S.ones(A.rows,1)
 def high(self,q):return [i for i in self.head if self.pure[i]>=q]
def mixed(A,b,P,degree,pure):
    """Paid moments + actual samples on the current physical prefix."""
    c=A*S.ones(A.rows,1);m=P-degree+1;eta=degree-m
    assert 0<=m<=degree and eta>=0
    o0=[[b[i]*c[i]**j for i in range(A.rows)]for j in range(m)]
    r0=[[R(1,i+j+1)for j in range(degree)]for i in range(m)]
    candidates=[i for i,r in pure.items() if r>=degree]
    for ids in combinations(candidates,eta):
        if len({c[i] for i in ids})!=eta:continue
        H=M(r0+[[c[i]**k for k in range(degree)]for i in ids])
        if not H.det():continue
        inv=H.inv();assert inv*H==S.eye(degree)
        O=M(o0+[[int(k==i)for k in range(A.rows)]for i in ids])
        return inv*O,ids
    raise ValueError(('failed mixed donor solve',P,degree,candidates))
def receiver(A,b,P,degree,pure,x,γ):
    D,_=mixed(A,b,P,degree,pure)
    jet=M([[x**(k+1)/(k+1)-γ*x**k for k in range(degree)]])
    return jet*D
def extend(src,terminal):
    A,b,P=src.A,src.b,src.p
    p=P+2; m=p//2; q=m-1 if terminal else m
    a=p-q-1; k=p-1; h=k-a; N=A.rows; γ=A[0,0];spare=int(terminal)
    donors=src.head if terminal else src.high(q+1)
    assert len(donors)<=h and all(src.pure[i]>=q+1 for i in donors)
    assert not terminal or len(donors)==h
    pins=[1-(2*i-1)*γ for i in reversed(range(1,a-spare+1))]
    dh=len(donors); sites=[src.c[i]for i in donors]
    add=h-dh-1 if not terminal else 0
    sites += [R(-100*p-2*j-1) for j in range(add)]
    F0=S.prod(X-t for t in sites+pins); z=integral(X*F0)/integral(F0)
    if terminal:sites.append(z)
    else:sites.insert(dh,z)   # first new low row may be used by later protected stages
    sites+=pins;assert len(sites)==len(set(sites))==k
    F=S.Poly(F0*(X-z),X)
    w=[integral(F.exquo(S.Poly(X-t,X)).as_expr())/F.diff().eval(t) for t in sites]
    assert all(w) and all(sum(v*t**j for t,v in zip(sites,w))==R(1,j+1) for j in range(p))
    defect=(p+1)*sum(v*t**p for t,v in zip(sites,w))-1; assert defect
    Newt=[S.Integer(1)]
    for t in reversed(sites):Newt.append(S.expand(Newt[-1]*(X-t)))
    LP=M([[v*val(f,t) for v,t in zip(w,sites)]for f in Newt])
    U=S.zeros(k,N);T=S.zeros(k);AP=A; pure=src.pure.copy();virtPure={}
    for j in range(h):
        if j<dh:
            r=donors[j]; strict=S.zeros(1,N+j);strict[:,:N]=A[r,:];strict[0,r]-=γ
            level=pure[r]
        else:
            wP=b.col_join(S.zeros(j,1))
            # Try the next-grade decoder first. The donor count is checked
            # against an already certified physical prefix, not a fake full block.
            try:
                strict=receiver(AP,wP,P,q+1,pure,sites[j],γ); level=q+2
            except ValueError:
                strict=receiver(AP,wP,P,q,pure,sites[j],γ); level=q+1
        AP=AP.row_join(S.zeros(AP.rows,1)).col_join(strict.row_join(M([[γ]])))
        pure[N+j]=level;virtPure[j]=level
        U[j,:]=strict[:,:N]
        if j:T[j,:j]=strict[:,N:]
    # Only the tail pivots receive the reverse Newton correction.
    for j in range(k):
        piv=list(range(max(h,j+1),k));d=len(piv)
        if d:
            rhs=M([-LP[i+1,j]/(i+1)for i in range(d)])-LP[:d,:h]*T[:h,j]
            v=LP.extract(range(d),piv).inv()*rhs
            for i,pivot in enumerate(piv):T[pivot,j]=v[i]
    B=T+γ*S.eye(k)
    assert all(LP[i,:]*T==-LP[i+1,:]/(i+1)for i in range(a))
    H=S.zeros(a,N); hpol=[]
    for j in range(a):
        v=S.integrate(Newt[j],X)
        oldpoly=S.Poly(v.subs(X,1)-v-γ*Newt[j]+Newt[j+1]/(j+1),X)
        hpol.append(oldpoly.as_expr())
        if j<a-spare:
            assert oldpoly.degree()<=j-1
            H[j,:]=M([[b[i]*oldpoly.eval(src.c[i])for i in range(N)]])
        else:
            assert terminal and j==a-1 and oldpoly.degree()<=j
            D,_=mixed(A,b,P,q+1,src.pure)
            H[j,:]=M([[integral(oldpoly.as_expr()*X**t)for t in range(q+1)]])*D
    U[h:,:]=LP[:a,h:].inv()*(H-LP[:a,:h]*U[:h,:])
    assert LP[:a,:]*U==H
    # Explicit finite low integrated-column gate on the weighted pivot rows.
    # The unweighted head rows pay the same formal target by the mixed recipes.
    E=M([[t**j for j in range(q)]for t in sites])
    EJ=M([[t**(j+1)/(j+1) for j in range(q)]for t in sites])
    hh=M([[integral(f*X**j)for j in range(q)]for f in hpol])
    assert hh+LP[:a,:]*B*E==LP[:a,:]*EJ
    # The power adjoint and its scalar payment are tested independently.
    C=M([[S.Poly(f,X).nth(i)for i in range(a)]for f in Newt[:a]])
    gp=M([[S.Poly(γ*Newt[j]-Newt[j+1]/(j+1),X).nth(i)
           for i in range(a+1)]for j in range(a)])
    g=C.inv()*gp
    hcoeff=M([[R(int(i==0)-int(i==j+1),j+1)-g[j,i]for i in range(a+1)]for j in range(a)])
    assert all(g[j,i]==0 for j in range(a) for i in range(j+2,a+1))
    assert all(hcoeff[j,i]==0 for j in range(a-spare)for i in range(j,a+1))
    for j in range(a):
        for n in range(q+1,p-j):
            assert n*sum((g[j,i]+hcoeff[j,i])*R(1,n+i)for i in range(a+1))==R(1,n+j+1)
    av=A.row_join(S.zeros(N,k)).col_join(U.row_join(B))
    bv=S.zeros(N,1).col_join(M(w))
    for j in reversed(range(dh)):
        r=donors[j];d1=av.row(r).copy();d2=av.row(N+j).copy()
        d1[r]-=γ;d2[N+j]-=γ;assert d1==d2
        av[:,r]+=av[:,N+j];bv[r]+=bv[N+j];av.row_del(N+j);av.col_del(N+j);bv.row_del(N+j)
    assert av.rows==N+k-dh and all(av[i,i]==γ and not any(av[i,j]for j in range(i+1,av.rows))for i in range(av.rows))
    nxt=donors+list(range(N,N+h-dh))
    pp=src.pure.copy()
    for j in range(dh,h):pp[N+j-dh]=virtPure[j]
    snew=Seed(av,bv,p,nxt,pp)
    assert [snew.c[i]for i in nxt]==sites[:h]
    # Actual scalar rule after redirect and any clock cancellations elsewhere.
    assert all(sum(bv[i]*snew.c[i]**j for i in range(av.rows))==R(1,j+1)for j in range(p))
    assert (p+1)*sum(bv[i]*snew.c[i]**p for i in range(av.rows))-1==defect
    return snew,defect,dh,virtPure,z
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('seed10',type=Path);parser.add_argument('--out',type=Path,default=Path('.'))
    parser.add_argument('--through',type=int,default=20,choices=(12,14,16,18,20))
    opt=parser.parse_args()
    t=json.loads(opt.seed10.read_text())
    assert t['order']==10 and t['stages']==22
    head=list(range(13,18))
    src=Seed(M(t['a_integer'])/t['a_denominator'],M(t['b_integer'])/t['b_denominator'],10,head,
             {j:(6 if j<=15 else 7)for j in head})
    assert [src.c[i]for i in head]==[R(-3),R(-5),R(-7),R(-9),R(8915889,8549164)]
    opt.out.mkdir(parents=True,exist_ok=True)
    for p in range(12,opt.through+1,2):
        st=time.monotonic()
        out,d,n,h,z=extend(src,True)
        save(out.A,out.b,p,d,opt.out)
        print(f'terminal order {p}: {out.A.rows} stages, {n} literal merges, defect sign {S.sign(d)}, exact arithmetic {time.monotonic()-st:.2f}s',flush=True)
        if p<opt.through:
            st=time.monotonic()
            src,d,n,h,z=extend(src,False)
            od=opt.out/f'prep-{p}';od.mkdir(exist_ok=True);save(src.A,src.b,p,d,od)
            print(f'prepare order {p}: {src.A.rows} stages, {n} literal merges, local head grades {list(h.values())}, exact arithmetic {time.monotonic()-st:.2f}s',flush=True)
if __name__=='__main__':main()
