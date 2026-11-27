"""The exact all-head terminal adjoint and low feed receipts for even p≥12."""
from pathlib import Path
from build_even12 import integral,val,R,M,X
from p12_receipts import matrixdef,vecdef
import json,sys,re
import sympy as S
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
def cert(p,base,term,donors,out):
    src=json.loads(base.read_text());end=json.loads(term.read_text())
    A=M(src['a_integer'])/src['a_denominator'];b=M(src['b_integer'])/src['b_denominator'];N=A.rows
    m=p//2;q=m-1;a=m;k=p-1;γ=R(1,4);assert len(donors)==q and A[0,0]==γ
    c=A*S.ones(N,1);fixed=[c[i]for i in donors]
    pl=[1-(2*i-1)*γ for i in reversed(range(1,a))]
    F0=S.prod(X-x for x in fixed+pl);z=integral(X*F0)/integral(F0)
    F=S.Poly(F0*(X-z),X);xs=fixed+[z]+pl;w=[integral(F.exquo(S.Poly(X-x,X)).as_expr())/F.diff().eval(x)for x in xs]
    P=[S.Integer(1)]
    for x in reversed(xs):P.append(S.expand(P[-1]*(X-x)))
    PN=M([[wi*val(f,x)for x,wi in zip(xs,w)]for f in P]);T=S.zeros(k)
    for j in range(k):
        piv=list(range(max(q,j+1),k));d=len(piv)
        if not d:continue
        r=PN.extract(range(d),piv).inv()*M([-PN[i+1,j]/(i+1)for i in range(d)])
        for i,pivot in enumerate(piv):T[pivot,j]=r[i]
    B=T+γ*S.eye(k)
    obs=M([[b[i]*c[i]**j for i in range(N)]for j in range(q)]+[[int(i==donors[0])for i in range(N)]])
    mix=M([[R(1,i+j+1)for j in range(m)]for i in range(q)]+[[c[donors[0]]**j for j in range(m)]])
    inv=mix.inv();D=inv*obs
    oldPred=M([[A[j,i]-(γ if i==j else 0)for i in range(N)]for j in donors])
    bank=obs.col_join(oldPred)
    C=M([[S.Poly(f,X).nth(j)for j in range(a)]for f in P[:a]])
    G=C.inv()*M([[S.Poly(γ*P[i]-P[i+1]/(i+1),X).nth(j)for j in range(a+1)]for i in range(a)])
    H=M([[R(int(j==0)-int(j==i+1),i+1)-G[i,j]for j in range(a+1)]for i in range(a)])
    T0=S.zeros(q,k)
    for i in range(q):T0[i,m+i]=1
    oldF=S.zeros(a,k);HP=C*H
    for i in range(a-1):oldF[i,:q]=HP[i,:q]
    oldF[a-1,:m]=M([[sum(HP[a-1,k]*R(1,k+j+1)for k in range(a+1))for j in range(m)]])*inv
    V=T0.col_join(PN[:a,q:].inv()*(oldF-PN[:a,:q]*T0));U=V*bank
    W=M([[v*x**j for v,x in zip(w,xs)]for j in range(a+1)])
    assert W[:a,:]*B==G*W
    W0=M([[b[i]*c[i]**j for i in range(N)]for j in range(a+1)]);H0=H*W0
    H0[a-1,:]=M([[sum(H[a-1,k]*R(1,k+j+1)for k in range(a+1))for j in range(m)]])*D
    assert H0==W[:a,:]*U
    E=M([[x**j for j in range(m)]for x in xs]);EI=M([[x**(j+1)/(j+1)for j in range(m)]for x in xs])
    R1=mix.col_join(M([[c[i]**(j+1)/(j+1)-γ*c[i]**j for j in range(m)]for i in donors]))
    assert (V*R1+B*E)[:,:q]==EI[:,:q]
    Av=A.row_join(S.zeros(N,k)).col_join(U.row_join(B));bv=S.zeros(N,1).col_join(M(w))
    for j,r in reversed(list(enumerate(donors))):
        aa=Av.row(r).copy();bb=Av.row(N+j).copy();aa[r]-=γ;bb[N+j]-=γ;assert aa==bb
        Av[:,r]+=Av[:,N+j];bv[r]+=bv[N+j];Av.row_del(N+j);Av.col_del(N+j);bv.row_del(N+j)
    assert Av==M(end['a_integer'])/end['a_denominator'] and bv==M(end['b_integer'])/end['b_denominator']
    label=f'Even{p}Data'
    s=f'''module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
@[expose] public section
namespace RKResearch.Certified.{label}
'''
    for name,v in [('Btail',B),('Utail',U),('feedMap',V),('G',G),('H',H),('inverse',inv)]:
        s+=matrixdef(name,v)
    for name,v in [('site',xs),('weights',w)]:s+=vecdef(name,v)
    (out/f'{label}.lean').write_text(s+f'end RKResearch.Certified.{label}\n')
    print(f'order {p}: exact adjoint/integrated feed and resulting {Av.rows} physical rows checked')
def main():
    p=int(sys.argv[1]);base=Path(sys.argv[2]);donors={14:[16,17,22,23,24,25],
        16:[23,24,25,31,32,33,34],18:[31,32,33,34,41,42,43,44],20:[41,42,43,44,52,53,54,55,56]}[p]
    cert(p,base/f'prep-{p-2}'/f'tableau-{p-2}.json',base/f'tableau-{p}.json',donors,Path(sys.argv[3]))
if __name__=='__main__':main()
