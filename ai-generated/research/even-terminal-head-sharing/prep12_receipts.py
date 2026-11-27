"""Emit the physical 31-stage even-order prep proof's exact finite matrices."""
from pathlib import Path
from p12_receipts import matrixdef,vecdef
from build_even12 import integral,val,R,M,X
import sys,json,sympy as S
def main(srcpath,outpath,targetpath):
    j=json.loads(Path(srcpath).read_text());A=M(j['a_integer'])/j['a_denominator'];b=M(j['b_integer'])/j['b_denominator'];N=A.rows
    γ=R(1,4);c=A*S.ones(N,1);d=[16,17];p=12;a=5;k=11;h=6
    pins=[1-(2*i-1)*γ for i in reversed(range(1,6))]
    extras=[R(-1201),R(-1203),R(-1205)]
    F0=S.prod(X-y for y in [c[i]for i in d]+extras+pins)
    z=integral(X*F0)/integral(F0);xs=[c[i]for i in d]+[z]+extras+pins
    F=S.Poly(F0*(X-z),X);w=[integral(F.exquo(S.Poly(X-y,X)).as_expr())/F.diff().eval(y)for y in xs]
    Newt=[S.Integer(1)]
    for y in reversed(xs):Newt.append(S.expand(Newt[-1]*(X-y)))
    LP=M([[u*val(f,y)for u,y in zip(w,xs)]for f in Newt])
    T=S.zeros(k)
    mw=M([[b[i]*c[i]**j for i in range(N)]for j in range(5)])
    point=[13,16,17]
    pointobs=M([[int(i==j)for i in range(N)]for j in point])
    strict=M([[A[i,j]-(γ if i==j else 0)for j in range(N)]for i in d])
    bank=mw.col_join(pointobs).col_join(strict)
    jet=lambda x,n:M([[x**(i+1)/(i+1)-γ*x**i for i in range(n)]])
    D6=M([[R(1,i+j+1)for j in range(6)]for i in range(5)]+[[c[13]**j for j in range(6)]]).inv()
    D7=M([[R(1,i+j+1)for j in range(7)]for i in range(4)]+[[ctr**j for j in range(7)]for ctr in [c[16],c[17],z]]).inv()
    HF=S.zeros(h,10)
    HF[0,8]=1;HF[1,9]=1
    HF[2,:6]=jet(z,6)*D6
    for i in range(3,h):
        v=jet(xs[i],7)*D7
        HF[i,:4]=v[:,:4];HF[i,6:8]=v[:,4:6];T[i,2]=v[6]
    for col in range(k):
        piv=list(range(max(h,col+1),k));n=len(piv)
        if not n:continue
        x=LP.extract(range(n),piv).inv()*(M([-LP[i+1,col]/(i+1)for i in range(n)])-LP[:n,:h]*T[:h,col])
        for j,u in enumerate(piv):T[u,col]=x[j]
    B=T+γ*S.eye(k)
    C=M([[S.Poly(f,X).nth(i)for i in range(a)]for f in Newt[:a]])
    G=C.inv()*M([[S.Poly(γ*Newt[i]-Newt[i+1]/(i+1),X).nth(j)for j in range(a+1)]for i in range(a)])
    H=M([[R(int(k==0)-int(k==j+1),j+1)-G[j,k]for k in range(a+1)]for j in range(a)])
    HH=(C*H).row_join(S.zeros(a,4))
    F=HF.col_join(LP[:a,h:].inv()*(HH-LP[:a,:h]*HF))
    U=F*bank
    E=M([[y**j for j in range(7)]for y in xs])
    EJ=M([[y**(j+1)/(j+1)for j in range(7)]for y in xs])
    O=M([[R(1,i+j+1)for j in range(7)]for i in range(5)]
        +[[c[i]**j for j in range(7)]for i in point]+[list(jet(c[i],7))for i in d])
    assert (F*O+B*E)[:,:6]==EJ[:,:6]
    assert (F*O+B*E)[3:6,:]==EJ[3:6,:]
    av=A.row_join(S.zeros(N,k)).col_join(U.row_join(B));bv=S.zeros(N,1).col_join(M(w))
    for i,r in reversed(list(enumerate(d))):
       av[:,r]+=av[:,N+i];bv[r]+=bv[N+i];av.row_del(N+i);av.col_del(N+i);bv.row_del(N+i)
    td=json.loads(Path(targetpath).read_text())
    assert av==M(td['a_integer'])/td['a_denominator'] and bv==M(td['b_integer'])/td['b_denominator']
    s='''module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
@[expose] public section
namespace RKResearch.Certified.EvenPrep12Data
'''
    for name,v in [('Btail',B),('Utail',U),('feedMap',F),('G',G),('H',H)]:s+=matrixdef(name,v)
    for name,v in [('site',xs),('weights',w)]:s+=vecdef(name,v)
    Path(outpath).write_text(s+'end RKResearch.Certified.EvenPrep12Data\n')
    print('Exact old-to-new, integrated columns, protected rows and literal prep12 bytes agree.')
if __name__=='__main__':main(*sys.argv[1:])
