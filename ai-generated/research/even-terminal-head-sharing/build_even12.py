"""Three exact two-order lifts to a 28-stage rational strict SDIRK of order 12.
Input: archived seven-stage rational strict SDIRK order-six numeral JSON.
"""
import argparse,json,math,sys
from pathlib import Path
from functools import lru_cache
import sympy as S
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
R=S.Rational; M=S.Matrix; X=S.Symbol('X')

def integral(P):
    return sum(v/(i+1) for (i,),v in S.Poly(P,X).terms())
def val(P,x):
    return S.Poly(P,X).eval(x)
@lru_cache(None)
def trees(p):
    ts=[()];sizes=[1]
    for n in range(2,p+1):
        N=len(sizes)
        def rec(rem,lo,kids):
            if not rem:yield tuple(kids);return
            for j in range(lo,N):
                if sizes[j]>rem:break
                yield from rec(rem-sizes[j],j,kids+[j])
        extra=list(rec(n-1,0,[]));ts+=extra;sizes += [n]*len(extra)
    return ts,sizes
def norm_features(A,n):
    ts,ns=trees(n);features=[];prim=[]
    for branchlist,m in zip(ts,ns):
        v=S.ones(A.rows,1)
        for i in branchlist:v=v.multiply_elementwise(prim[i])
        features.append(v);prim.append(m*A*v)
    return M.hstack(*features),ns
def strict_feed(A,x,gamma,through):
    E,ns=norm_features(A,through-1)
    ideal=M([[x**n/n-gamma*x**(n-1)for n in ns]])
    cols=list(E.rref()[1]);rows=list(E[:,cols].T.rref()[1])
    coeff=ideal[:,cols]*E.extract(rows,cols).inv()
    v=S.zeros(1,A.rows)
    for j,i in enumerate(rows):v[0,i]=coeff[j]
    assert v*E==ideal,('predecessor profile not payable',x,through)
    return v
def dense_decoder(A,b,oldp,n,donor_ids):
    c=A*S.ones(A.rows,1); ma=oldp-n+1
    assert n==ma+len(donor_ids)
    OBS=M([[b[i]*c[i]**j for i in range(A.rows)]for j in range(ma)]+[
        [int(i==j)for i in range(A.rows)]for j in donor_ids])
    H=M([[R(1,i+j+1)for j in range(n)]for i in range(ma)]+[[c[i]**j for j in range(n)]for i in donor_ids])
    D=H.inv()*OBS
    E,ns=norm_features(A,n)
    exp=M(n,len(ns),lambda i,j:int(i==ns[j]-1))
    assert D*E==exp
    return D
def lift(A,b,p,q,head,frees,*,spare=0,decoder=None):
    """frees are actual independent head sites besides solved z;
    if spare=1, z is instead the first pivot and independent sites fill entire head.
    q is old low branch cutoff. An optional stronger decoder pays final pivot.
    """
    N=A.rows; a=p-q-1;cc=A*S.ones(N,1);γ=A[0,0]
    pins=[1-(2*i-1)*γ for i in reversed(range(1,a-spare+1))]
    initial=list(frees)+pins
    f=S.prod(X-x for x in initial)
    z=integral(X*f)/integral(f);xs=list(frees)+[z]+pins
    k=len(xs);h=k-a
    assert len(set(xs))==k==p-1 and h==len(head)
    F=S.Poly(f*(X-z),X)
    w=[integral(F.exquo(S.Poly(X-x,X)).as_expr())/F.diff().eval(x) for x in xs]
    assert all(w) and all(sum(wi*x**j for wi,x in zip(w,xs))==R(1,j+1) for j in range(p))
    defect=(p+1)*sum(wi*x**p for wi,x in zip(w,xs))-1
    assert defect
    P=[S.Integer(1)]
    for x in reversed(xs):P.append(S.expand(P[-1]*(X-x)))
    LP=M([[wi*val(Pj,x)for x,wi in zip(xs,w)]for Pj in P])
    SS=S.zeros(k);U=S.zeros(k,N);AA=A;merges={}
    for j,(mode,arg) in enumerate(head):
        if mode=='old':
            assert xs[j]==cc[arg]
            v=S.zeros(1,N+j);v[0,:N]=A[arg,:];v[arg]-=γ;merges[j]=arg
        else:
            v=strict_feed(AA,xs[j],γ,arg)
        AA=AA.row_join(S.zeros(AA.rows,1)).col_join(v.row_join(M([[γ]])))
        U[j,:]=v[:,:N]
        if j:SS[j,:j]=v[:,N:]
    for j in range(k):
        piv=list(range(max(h,j+1),k));d=len(piv)
        if d:
            rhs=M([-LP[i+1,j]/(i+1)for i in range(d)])-LP[:d,:h]*SS[:h,j]
            t=LP.extract(range(d),piv).inv()*rhs
            for i,row in enumerate(piv):SS[row,j]=t[i]
    assert all(LP[i,:]*SS==-LP[i+1,:]/(i+1)for i in range(a))
    H=S.zeros(a,N)
    for j in range(a):
        JP=S.integrate(P[j],X)
        pH=S.Poly(JP.subs(X,1)-JP-γ*P[j]+P[j+1]/(j+1),X)
        assert pH.degree()<=j
        if j<a-spare:
            assert pH.degree()<=j-1
            H[j,:]=M([[b[i]*pH.eval(cc[i])for i in range(N)]])
        else:
            assert decoder is not None and decoder.rows>=p-j-1
            H[j,:]=M([[integral(pH.as_expr()*X**i)for i in range(decoder.rows)]])*decoder
    U[h:,:]=LP[:a,h:].inv()*(H-LP[:a,:h]*U[:h,:])
    B=SS+γ*S.eye(k)
    Avirt=A.row_join(S.zeros(N,k)).col_join(U.row_join(B));vW=S.zeros(N,1).col_join(M(w))
    AA=Avirt.copy();bW=vW.copy()
    for j,r in sorted(merges.items(),reverse=True):
        jj=N+j
        d1=AA.row(r).copy();d2=AA.row(jj).copy();d1[r]-=γ;d2[jj]-=γ
        assert d1==d2
        AA[:,r]+=AA[:,jj];bW[r]+=bW[jj];AA.row_del(jj);AA.col_del(jj);bW.row_del(jj)
    inds=[merges[j]if j in merges else N+j-sum(i<j for i in merges)for j in range(h)]
    return AA,bW,xs,inds,defect
def save(A,b,p,defect,out):
    d=math.lcm(*(int(x.q)for x in A)); e=math.lcm(*(int(x.q)for x in b))
    dat=dict(order=p,stages=A.rows,common_diagonal=str(A[0,0]),
        a_denominator=d,b_denominator=e,a_integer=[[int(d*x)for x in A.row(i)]for i in range(A.rows)],
        b_integer=[int(e*x)for x in b],next_bush_defect=str(defect))
    (out/f'tableau-{p}.json').write_text(json.dumps(dat,indent=1)+'\n')
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('seed',type=Path);ap.add_argument('--out',type=Path,default=Path('.'));o=ap.parse_args()
    t=json.loads(o.seed.read_text());A=M(t['a_integer'])/t['a_denominator'];b=M(t['b_integer'])/t['b_denominator']
    assert A.shape==(7,7) and A[0,0]==R(1,4)
    A,b,sites,idx,d=lift(A,b,8,3,[('old',4),('new',4),('new',5)],[R(1,2),R(-1)])
    print('order 8:',A.rows,'rows, head clocks',sites[:3],'cleared defect',d,flush=True);save(A,b,8,d,o.out)
    dense_decoder(A,b,8,5,[idx[2]])
    A,b,sites,idx,d=lift(A,b,10,5,[('new',6),('new',6),('new',6),('new',7),('new',7)],
                         [R(-3),R(-5),R(-7),R(-9)])
    print('order 10:',A.rows,'rows, head clocks',sites[:5],'cleared defect',d,flush=True);save(A,b,10,d,o.out)
    D=dense_decoder(A,b,10,6,[idx[0]])
    A,b,sites,idx,d=lift(A,b,12,5,[('old',i)for i in idx],sites[:5],spare=1,decoder=D)
    print('order 12:',A.rows,'rows, head clocks',sites[:5],'solved pivot',sites[5],'cleared defect',d,flush=True);save(A,b,12,d,o.out)
if __name__=='__main__':main()
