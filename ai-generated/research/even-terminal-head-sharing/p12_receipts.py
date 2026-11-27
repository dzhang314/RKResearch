"""Generate exact finite matrix receipts for the symbolic 28-stage order-12 witness."""
from pathlib import Path
from build_even12 import integral,val,save,R,M,X
import json,sys,argparse,sympy as S
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
def matrixdef(name,A):
    ex=lambda y:str(y.p) if y.q==1 else f'({y.p} / {y.q} : ℚ)'
    rows=',\n  '.join('#['+', '.join(ex(R(x))for x in A.row(i))+']'for i in range(A.rows))
    return f'def {name}Rows : Array (Array ℚ) := #[\n  {rows}\n]\ndef {name} : Matrix (Fin {A.rows}) (Fin {A.cols}) ℚ := fun i j => ({name}Rows[i.val]!)[j.val]!\n'
def vecdef(name,xx):
    ex=lambda y:str(y.p) if y.q==1 else f'({y.p} / {y.q} : ℚ)'
    a=', '.join(ex(R(x))for x in xx)
    return f'def {name}Vec : Array ℚ := #[{a}]\ndef {name} (i : Fin {len(xx)}) : ℚ := {name}Vec[i.val]!\n'
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('seed10',type=Path)
    ap.add_argument('literal12',type=Path);ap.add_argument('--out',type=Path,default=Path('.'));o=ap.parse_args()
    src=json.loads(o.seed10.read_text());end=json.loads(o.literal12.read_text())
    A=M(src['a_integer'])/src['a_denominator'];b=M(src['b_integer'])/src['b_denominator'];N=22
    γ=R(1,4);assert A.rows==N and A[0,0]==γ
    c=A*S.ones(N,1);ds=list(range(13,18));fixed=[c[i]for i in ds]
    pl=[1-(2*i-1)*γ for i in reversed(range(1,6))]
    F0=S.prod(X-x for x in fixed+pl);z=integral(X*F0)/integral(F0)
    F=S.Poly(F0*(X-z),X);xs=fixed+[z]+pl;w=[integral(F.exquo(S.Poly(X-x,X)).as_expr())/F.diff().eval(x)for x in xs]
    P=[S.Integer(1)]
    for x in reversed(xs): P.append(S.expand(P[-1]*(X-x)))
    PN=M([[wi*val(f,x)for x,wi in zip(xs,w)]for f in P]);T=S.zeros(11)
    for j in range(11):
        piv=list(range(max(5,j+1),11));d=len(piv)
        if not d:continue
        r=PN.extract(range(d),piv).inv()*M([-PN[i+1,j]/(i+1)for i in range(d)])
        for i,pivot in enumerate(piv):T[pivot,j]=r[i]
    B=T+γ*S.eye(11)
    obs=M([[b[i]*c[i]**j for i in range(N)]for j in range(5)]+[[int(i==13)for i in range(N)]])
    mix=M([[R(1,i+j+1)for j in range(6)]for i in range(5)]+[[(-3)**k for k in range(6)]])
    inv=mix.inv();D=inv*obs
    oldPred=M([[A[k,i]-(γ if i==k else 0)for i in range(N)]for k in ds])
    bank=obs.col_join(oldPred)
    C=M([[S.Poly(f,X).nth(j)for j in range(6)]for f in P[:6]])
    G=C.inv()*M([[S.Poly(γ*P[i]-P[i+1]/(i+1),X).nth(j)for j in range(7)]for i in range(6)])
    H=M([[R(int(k==0)-int(k==j+1),j+1)-G[j,k]for k in range(7)]for j in range(6)])
    T0=S.zeros(5,11)
    for i in range(5):T0[i,6+i]=1
    oldF=S.zeros(6,11)
    HP=C*H
    for i in range(5):oldF[i,:5]=HP[i,:5]
    oldF[5,:6]=M([[sum(HP[5,k]*R(1,k+j+1)for k in range(7))for j in range(6)]])*inv
    V=T0.col_join(PN[:6,5:].inv()*(oldF-PN[:6,:5]*T0))
    U=V*bank
    W=M([[v*x**j for v,x in zip(w,xs)]for j in range(7)])
    assert W[:6,:]*B==G*W
    W0=M([[b[i]*c[i]**j for i in range(N)]for j in range(7)])
    H0=H*W0
    H0[5,:]=M([[sum(H[5,k]*R(1,k+j+1)for k in range(7))for j in range(6)]])*D
    assert H0==W[:6,:]*U
    E=M([[x**j for j in range(6)]for x in xs]);EI=M([[x**(j+1)/(j+1)for j in range(6)]for x in xs])
    R1=mix.col_join(M([[c[i]**(j+1)/(j+1)-γ*c[i]**j for j in range(6)]for i in ds]))
    assert (V*R1+B*E)[:,:5]==EI[:,:5]
    Av=A.row_join(S.zeros(N,11)).col_join(U.row_join(B));bv=S.zeros(N,1).col_join(M(w))
    for j,r in reversed(list(enumerate(ds))):
        aa=Av.row(r).copy();bb=Av.row(N+j).copy();aa[r]-=γ;bb[N+j]-=γ;assert aa==bb
        Av[:,r]+=Av[:,N+j];bv[r]+=bv[N+j];Av.row_del(N+j);Av.col_del(N+j);bv.row_del(N+j)
    assert Av==M(end['a_integer'])/end['a_denominator'] and bv==M(end['b_integer'])/end['b_denominator']
    s='''module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
@[expose] public section
namespace RKResearch.Certified.Even12Data
'''
    for name,v in [('Btail',B),('Utail',U),('feedMap',V),('G',G),('H',H),('inverse',inv)]:
        s+=matrixdef(name,v)
    for name,v in [('site',xs),('weights',w)]:s+=vecdef(name,v)
    (o.out/'Even12Data.lean').write_text(s+'end RKResearch.Certified.Even12Data\n')
    print('All finite action identities and the already frozen physical tableau checked exactly.')
if __name__=='__main__':main()
