"""Exact Newton-tail order-13 fixture from the unchanged fixed-one order-11 witness.
No rooted-tree enumeration: verify the four finite matrix/polynomial certificates.
Usage: python3 gen_symbolic13.py tableau-11.json --out OUTPUT_DIRECTORY
"""
import argparse, json, math, sys
from pathlib import Path
from functools import reduce
import sympy as S
R=S.Rational; Mat=S.Matrix; x=S.Symbol('x')
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def integ(f):
    return sum(a/(k+1) for (k,),a in S.Poly(f,x).terms())
def at(f,z):
    return S.Poly(f,x).eval(z)
def polcoeffs(f,q):
    p=S.Poly(f,x);return [p.nth(i) for i in range(q+1)]
def arr(q):
    return '#['+', '.join(map(str,q))+']'
def qexpr(y):
    y=R(y);return str(y.p) if y.q==1 else f'({y.p} / {y.q} : ℚ)'
def leanArray(name,data):
    if not isinstance(data,S.MatrixBase):
        return f'def {name} : Array ℚ := '+arr([qexpr(y) for y in data])+'\n'
    return f'def {name} : Array (Array ℚ) := #[\n  '+',\n  '.join(arr([qexpr(y) for y in data.row(i)]) for i in range(data.rows))+'\n]\n'
def matrixDef(name,M):
    return leanArray('raw'+name,M)+f'def {name} : Matrix (Fin {M.rows}) (Fin {M.cols}) ℚ := fun i j => (raw{name}[i.val]!)[j.val]!\n'
def vecDef(name,v):
    return leanArray('raw'+name,list(v))+f'def {name} (i : Fin {len(v)}) : ℚ := raw{name}[i.val]!\n'
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('seed',type=Path);p.add_argument('--out',type=Path,default=Path('.'));args=p.parse_args()
    t=json.loads(args.seed.read_text()); old=Mat(t['a_integer'])/t['a_denominator']; w0=Mat(t['b_integer'])/t['b_denominator']; n0=old.rows
    q=6;n=12;d0=[18,19,20]; c0=old*S.ones(n0,1); a=[c0[i] for i in d0]
    assert n0==26 and old[0,0]==1 and a==[R(-9),R(-11),R(251647454237400205,337389807870474227)]
    pins=[R(2-2*i) for i in reversed(range(1,q+1))]
    fixed=a+[R(-1301),R(-1303)]+pins
    F0=S.prod(x-z for z in fixed)
    z=integ(x*F0)/integ(F0); cs=fixed[:5]+[z]+pins
    assert len(set(cs))==n
    F=F0*(x-z); w=[integ(S.div(F,x-c,x)[0])/S.diff(F,x).subs(x,c) for c in cs]
    Q=Mat([[a*c**i for a,c in zip(w,cs)] for i in range(q+1)])
    assert all(w) and all(sum(a*c**j for a,c in zip(w,cs))==R(1,j+1) for j in range(13))
    nextDefect=14*sum(a*c**13 for a,c in zip(w,cs))-1;assert nextDefect
    ps=[S.Integer(1)]
    for v in reversed(cs):ps.append(S.expand(ps[-1]*(x-v)))
    PL=Mat([[a*at(P,c) for a,c in zip(w,cs)] for P in ps])
    T=S.zeros(n)
    for j in range(n):
        piv=list(range(max(q,j+1),n))
        m=len(piv)
        if m:
            v=PL.extract(range(m),piv).inv()*Mat([-PL[i+1,j]/(i+1) for i in range(m)])
            for ii,k in enumerate(piv):T[k,j]=v[ii]
    assert all(PL[j,:]*T==-PL[j+1,:]/(j+1) for j in range(q))
    B=T+S.eye(n)
    cp=Mat([polcoeffs(P,q-1) for P in ps[:q]])
    gp=Mat([polcoeffs(ps[i]-ps[i+1]/(i+1),q) for i in range(q)])
    g=cp.inv()*gp
    h=Mat([[((1 if k==0 else 0)-(1 if k==j+1 else 0))*R(1,j+1)-g[j,k]
            for k in range(q+1)]for j in range(q)])
    assert all(g[j,k]==0 for j in range(q) for k in range(j+2,q+1))
    assert all(h[j,k]==0 for j in range(q) for k in range(j,q+1))
    assert Q[:q,:]*B==g*Q
    for r in range(q):
        for m in range(q+1,2*q-r+1):
            assert m*sum((g[r,k]+h[r,k])*R(1,m+k) for k in range(q+1))==R(1,m+r+1)
    Gshell=cp*h
    bank0=Mat([[w0[j]*c0[j]**i for j in range(n0)] for i in range(q-1)])
    donorEval=Mat([[int(j==i) for j in range(n0)] for i in d0[:2]])
    donorPred=Mat([[old[i,j]-int(i==j) for j in range(n0)] for i in d0])
    bank=bank0.col_join(donorEval).col_join(donorPred)
    mix=Mat([[R(1,i+k+1) for k in range(q+1)] for i in range(q-1)]+[[v**k for k in range(q+1)] for v in a[:2]])
    RF=lambda c: [c**(k+1)/(k+1)-c**k for k in range(q+1)]
    resp=mix.col_join(Mat([RF(v) for v in a]))
    inv=mix.inv()
    headF=S.zeros(q,q+1+len(d0))
    for i in range(3):headF[i,q+1+i]=1
    for i in range(3,6):headF[i,:q+1]=Mat([RF(cs[i])])*inv
    RHS=Gshell.row_join(S.zeros(q,len(d0)))
    FT=headF.col_join(PL[:q,q:].inv()*(RHS-PL[:q,:q]*headF))
    U=FT*bank
    ev=Mat([[v**k for k in range(q+1)] for v in cs])
    evI=Mat([[v**(k+1)/(k+1) for k in range(q+1)] for v in cs])
    assert (FT*resp+B*ev)[:,:q]==evI[:,:q]
    Qold=Mat([[w0[j]*c0[j]**i for j in range(n0)] for i in range(q+1)])
    assert Q[:q,:]*U==h*Qold
    A=old.row_join(S.zeros(n0,n)).col_join(U.row_join(B))
    bo=S.zeros(n0,1).col_join(Mat(w))
    for i in reversed(range(len(d0))):
        j=n0+i;r=d0[i]
        src=A.row(j).copy();dst=A.row(r).copy();src[j]-=1;dst[r]-=1
        assert src==dst
        A[:,r]+=A[:,j];bo[r]+=bo[j];A.row_del(j);A.col_del(j);bo.row_del(j)
    assert A.rows==35 and all(A[i,i]==1 and not any(A[i,j] for j in range(i+1,A.rows)) for i in range(A.rows))
    out=args.out;out.mkdir(parents=True,exist_ok=True)
    ad=math.lcm(*(int(z.q) for z in A));bd=math.lcm(*(int(z.q) for z in bo))
    dat=dict(order=13,stages=35,common_diagonal="1",a_denominator=ad,b_denominator=bd,
             a_integer=[[int(ad*z) for z in A.row(i)] for i in range(A.rows)],b_integer=[int(bd*z) for z in bo],
             next_bush_defect=str(nextDefect))
    (out/'tableau-13.json').write_text(json.dumps(dat,indent=1)+'\n')
    code='''module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul

@[expose] public section
namespace RKResearch.Certified.Symbolic13Data
'''
    for name, value in [('blockU',U),('blockB',B),('G',g),('H',h),('feedCoeffs',FT),('mixInv',inv)]:
        code+=matrixDef(name,value)
    for name,v in [('weights',w),('site',cs)]:
        code+=vecDef(name,v)
    code+='end RKResearch.Certified.Symbolic13Data\n'
    (out/'Symbolic13Data.lean').write_text(code)
    print('order 13: retained 26, virtual 12, literal merges 3, physical 35')
    print('solved clock',z,'next cleared bush',nextDefect)
if __name__=='__main__':main()
