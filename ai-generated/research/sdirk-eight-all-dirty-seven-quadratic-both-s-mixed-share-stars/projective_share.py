"""Projective necessary rows in the shared both-S mixed prefix frame."""
from pathlib import Path
import sys
prior=Path(__file__).resolve().parent.parent/'sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank'
sys.path.insert(0,str(prior))
from mixed_share_common import F,frame,ip,strip
def mul(x,y):
    out=[F() for j in range(len(x)+len(y)-1)]
    for i,a in enumerate(x):
      for j,b in enumerate(y):out[i+j]+=a*b
    return out
def compose0(P,z0,z1):
    t=[F()]
    for q in reversed(P):
        t=mul(t,[z0,z1]);t[0]+=q
    return t[:-1]
def projective(P,A,B):
    n=len(P)-1
    t=F()
    for i,c in enumerate(P):t+=c*(-A)**i*B**(n-i)
    return t
def regular(mode):
    lines,eq,gg,data=frame(mode)
    A,B,C,D=lines
    H,p,q,t,fp,fq,rp,rt,L3,L4,M,z0,z1,beta=data
    m0,m1,m2,m3=M
    G=[-m0+H*z0*(m2+m3*(z0+H)),
       m0+H*z1*(m2+m3*(2*z0+H)), H*m3*z1*z1]
    J=compose0(M,z0,z1)
    assert len(J)==4
    out=[A*D-C*B,projective(G,A,B),projective(J,A,B),
        projective(G,C,D),projective(J,C,D)]
    allg=sum(gg.values(),[])
    assert all(strip(ip(a.d),allg).total_degree()==0 for a in G+J+out)
    return list(map(eq,out)),gg
def regular_projection(mode,method=None):
    rows,groups=regular(mode)
    E=rows[0]
    print(mode,'projective rows',[p.degrees() for p in rows],flush=True)
    assert E
    hs=[a for a in sum(groups.values(),[]) if not a.degrees()[1]]
    if method is None:method=lambda a,b:a.resultant(b,'d')
    P=[strip(method(E,z),hs) for z in rows[1:]]
    Q=None
    for p in P:
        if p:Q=p if Q is None else Q.gcd(p)
    assert Q
    print(mode,'projection degrees',[p.total_degree() for p in P if p],
          'u factors',[(a.total_degree(),k) for a,k in Q.factor()[1]],flush=True)
    return Q.factor()[1],rows,groups,[p.total_degree() for p in P if p]
