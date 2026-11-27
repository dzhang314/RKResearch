"""Emit exact finite Lean receipts for the 14/16/18 even preparation steps."""
from pathlib import Path
from p12_receipts import matrixdef,vecdef
from build_even12 import integral,val,R,M,X
import sys,json,sympy as S
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def tableau(path):
    t=json.loads(path.read_text())
    return M(t['a_integer'])/t['a_denominator'],M(t['b_integer'])/t['b_denominator']

def cert(p,root,outpath):
    A,b=tableau(root/f'prep-{p-2}'/f'tableau-{p-2}.json')
    target=tableau(root/f'prep-{p}'/f'tableau-{p}.json')
    donors={14:[23,24,25],16:[31,32,33,34],18:[41,42,43,44]}[p]
    m=p//2; a=m-1; k=p-1; d=len(donors); N=A.rows; g=R(1,4); c=A*S.ones(N,1)
    pins=[1-(2*i-1)*g for i in reversed(range(1,a+1))]
    extras=[R(-100*p-2*i-1) for i in range(m-d-1)]
    cs=[c[i] for i in donors]
    F0=S.prod(X-y for y in cs+extras+pins)
    z=integral(X*F0)/integral(F0); xs=cs+[z]+extras+pins
    Fx=S.Poly(F0*(X-z),X)
    w=[integral(Fx.exquo(S.Poly(X-y,X)).as_expr())/Fx.diff().eval(y) for y in xs]
    newt=[S.Integer(1)]
    for x in reversed(xs):
        newt.append(S.expand(newt[-1]*(X-x)))
    LP=M([[v*val(f,x)for v,x in zip(w,xs)]for f in newt])
    T=S.zeros(k)
    for j in range(k):
        idx=list(range(max(m,j+1),k)); n=len(idx)
        if n:
            v=LP.extract(range(n),idx).inv()*M([-LP[i+1,j]/(i+1)for i in range(n)])
            for i,ii in enumerate(idx):T[ii,j]=v[i]
    B=T+g*S.eye(k)
    MW=M([[b[i]*c[i]**j for i in range(N)]for j in range(m-2)])
    points=M([[int(i==j) for i in range(N)]for j in donors[:3]])
    pred=M([[A[i,j]-(g if i==j else 0)for j in range(N)]for i in donors])
    bank=MW.col_join(points).col_join(pred)
    mix=M([[R(1,i+j+1)for j in range(m+1)]for i in range(m-2)]
        +[[x**j for j in range(m+1)]for x in cs[:3]])
    D=mix.inv();assert D*mix==S.eye(m+1)
    jet=lambda x:[x**(j+1)/(j+1)-g*x**j for j in range(m+1)]
    HF=S.zeros(m,m+1+d)
    for i in range(d):HF[i,m+1+i]=1
    for i in range(d,m):HF[i,:m+1]=M([jet(xs[i])])*D
    C=M([[S.Poly(f,X).nth(i)for i in range(a)]for f in newt[:a]])
    G=C.inv()*M([[S.Poly(g*newt[i]-newt[i+1]/(i+1),X).nth(j)for j in range(a+1)]for i in range(a)])
    H=M([[R(int(j==0)-int(j==i+1),i+1)-G[i,j]for j in range(a+1)]for i in range(a)])
    assert all(H[i,j]==0 for i in range(a) for j in range(i,a+1))
    HH=(C*H)[:,:m-2].row_join(S.zeros(a,3+d))
    F=HF.col_join(LP[:a,m:].inv()*(HH-LP[:a,:m]*HF))
    U=F*bank
    WG=M([[t*x**j for t,x in zip(w,xs)]for j in range(a+1)])
    W0=M([[b[i]*c[i]**j for i in range(N)]for j in range(a+1)])
    assert WG[:a,:]*B==G*WG and WG[:a,:]*U==H*W0
    E=M([[x**j for j in range(m+1)]for x in xs])
    EJ=M([[x**(j+1)/(j+1)for j in range(m+1)]for x in xs])
    Obs=mix.col_join(M([jet(x)for x in cs]))
    assert (F*Obs+B*E)[:,:m]==EJ[:,:m]
    assert (F*Obs+B*E)[d:m,:]==EJ[d:m,:]
    av=A.row_join(S.zeros(N,k)).col_join(U.row_join(B));bv=S.zeros(N,1).col_join(M(w))
    for j,i in reversed(list(enumerate(donors))):
        c1=av.row(i).copy();c2=av.row(N+j).copy();c1[i]-=g;c2[N+j]-=g;assert c1==c2
        av[:,i]+=av[:,N+j];bv[i]+=bv[N+j];av.row_del(N+j);av.col_del(N+j);bv.row_del(N+j)
    assert (av,bv)==target
    label=f'EvenPrep{p}Data'
    s=f"""module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
@[expose] public section
namespace RKResearch.Certified.{label}
"""
    for name,v in [('Btail',B),('Utail',U),('feedMap',F),('G',G),('H',H)]:s+=matrixdef(name,v)
    for name,v in [('site',xs),('weights',w)]:s+=vecdef(name,v)
    (outpath/f'{label}.lean').write_text(s+f'end RKResearch.Certified.{label}\n')
    print(f'prepare {p}: adjoints, integrated low columns and high rows, literal copies and {av.rows} output rows checked',flush=True)

if __name__=='__main__':
    cert(int(sys.argv[1]),Path(sys.argv[2]),Path(sys.argv[3]))
