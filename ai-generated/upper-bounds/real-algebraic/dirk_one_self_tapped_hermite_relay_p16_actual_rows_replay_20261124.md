# Actual twenty-seven-row Hermite late-receiver replay

Companion to `dirk_one_self_tapped_hermite_relay_p16_and_sharp_canonical_dense_stems_20261124.md`. First run this Python 3 / SymPy certificate for the exact branch enclosure used by the forward chart. It is the seven-proper-site case of the existing independently audited tilt certificate, with the stronger explicit bound on the actual root displacement obtained from the contraction inequality.

```python
import sympy as S
from fractions import Fraction as F
x=S.symbols('x');Q=S.Rational
def FF(m,N):
 ps=[S.Poly(x*(x-1)*S.jacobi(j,1,1,2*x-1),x) for j in range(m,m+N)]
 cs=[[int(z) for z in reversed(p.all_coeffs())] for p in ps]
 assert all(sum(a*x**j for j,a in enumerate(row))==p.as_expr() for p,row in zip(ps,cs))
 def E(t):return [sum((c*t**j for j,c in enumerate(row)),0*t) for row in cs]
 def I(t):return [sum((c*t**(j+1)/(j+1) for j,c in enumerate(row)),0*t) for row in cs]
 return E,I
def solve(M,v):
 import copy
 n=len(v);a=[list(z)+[rhs] for z,rhs in zip(zip(*M),v)]
 for j in range(n):
  def val(s):
   if isinstance(s,Z):
    return min(abs(s.v.lo),abs(s.v.hi)) if s.v.lo*s.v.hi>0 else 0
   return abs(s)
  i=max(range(j,n),key=lambda i:val(a[i][j]));assert val(a[i][j])>0
  a[i],a[j]=a[j],a[i];p=a[j][j];a[j]=[t/p for t in a[j]]
  for i in range(n):
   if i!=j:
    t=a[i][j];a[i]=[w-t*z for w,z in zip(a[i],a[j])]
 return [r[-1] for r in a]
def aa(x,y,f):return [a+f*b for a,b in zip(x,y)]
def calc(m,v,r,s,b,c,d):
 E,I=FF(m,5);e,i=FF(m+1,3);ev,er,es,eb,ec,ed=map(E,[v,r,s,b,c,d]);ib,ic=I(b),I(c)
 h=solve([e(v),i(v),e(r)],i(r))[1]
 solve([e(v),e(r),e(s)],i(s))
 R=aa(er,ev,-h)
 coeff=solve([R,es,ev,eb,ec],ic)
 k=-coeff[2]/coeff[1];B=aa(es,ev,-k)
 M=[R,B,eb];first=solve([row[:3] for row in M],ib[:3])
 res=[ib[j]-sum([row[j]*w for row,w in zip(M,first)]) for j in (3,4)]
 solve([R,B,eb,ec,ed],I(d))
 return res,h,k
settings=[
 (1,6,(6,4,5,1),(0.966133679253857,0.7995701941153093)),
 (1,7,(7,6,5,4),(0.9778058975527576,-0.4582246100150328)),
 (3,9,(4,3,2,1),(0.0751156227154861,0.47038751808391244)),
 (2,8,(4,3,2,1),(0.8919197393344899,0.47897292170417494))]
K=1<<660
class V:
 def __init__(s,a=0,b=None):
  if isinstance(a,V):s.lo,s.hi=a.lo,a.hi;return
  a=F(a);b=a if b is None else F(b);s.lo=a.numerator*K//a.denominator;s.hi=-((-b.numerator*K)//b.denominator)
 @classmethod
 def raw(c,l,u):v=c();v.lo=l;v.hi=u;return v
 def __add__(a,b):b=V(b);return V.raw(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return V.raw(-a.hi,-a.lo)
 def __sub__(a,b):return a+-V(b)
 def __rsub__(a,b):return V(b)+-a
 def __mul__(a,b):
  b=V(b);p=[x*y for x in (a.lo,a.hi) for y in (b.lo,b.hi)];return V.raw(min(p)//K,-((-max(p))//K))
 __rmul__=__mul__
 def __truediv__(a,b):
  b=V(b);assert b.lo*b.hi>0
  return a*V.raw(K*K//b.hi,-((-K*K)//b.lo))
 def __rtruediv__(a,b):return V(b)/a
 def __pow__(a,n):return V(1) if not n else (a*a)**(n//2)*(a if n%2 else 1)
def norm(a):return F(max(abs(a.lo),abs(a.hi)),K)
def mid(a):return F(a.lo+a.hi,2*K)
class Z:
 def __init__(s,a=0,g=None):
  if isinstance(a,Z):s.v,s.g=a.v,a.g;return
  s.v=V(a);s.g=[V(z) for z in (g if g is not None else (0,0))]
 def __add__(a,b):b=Z(b);return Z(a.v+b.v,[z+t for z,t in zip(a.g,b.g)])
 __radd__=__add__
 def __neg__(a):return Z(-a.v,[-g for g in a.g])
 def __sub__(a,b):return a+-Z(b)
 def __rsub__(a,b):return Z(b)+-a
 def __mul__(a,b):b=Z(b);return Z(a.v*b.v,[a.v*t+b.v*w for t,w in zip(b.g,a.g)])
 __rmul__=__mul__
 def __truediv__(a,b):
  b=Z(b);q=a.v/b.v;return Z(q,[(g-q*t)/b.v for g,t in zip(a.g,b.g)])
 def __rtruediv__(a,b):return Z(b)/a
 def __pow__(a,n):return Z(1) if n==0 else Z(a.v**n,[n*a.v**(n-1)*g for g in a.g])
C=[
('0.966133679254168737752396199515977884317843133489672426170204934422073205924639364417622', '0.799570194115575507988510385981439213447970931425044517981308072219328590470225946713939'),
('0.977805897551902537853703311306170191685702032435997116498430429947247888152481379996063', '-0.458224610015433205871080595712990749276174198339611828714810304412624468841399015909507'),
('0.075115622715411886387940962872458444715203475621588733238472758606303834386483338190582', '0.470387518083562118195367357246401266421028381788347412726976126039214338186134185080868'),
('0.891919739334470950022482906062730137859491356644510235883830920057989674559791550241123', '0.478972921704394903395787680270370880031759204438164145728132940441315148695912223005672')]
rad=F(1,10**42)
for (m,n,ids,_),cc in zip(settings[1:2],C[1:2]):
 cs=[F(z) for z in cc];gr=[Z(V(F(g[0]),F(g[1]))) for g,mul in S.Poly(S.jacobi(n,1,1,2*x-1),x).intervals(eps=Q(1,10**153))]
 a,b,c,d=[gr[j-1] for j in ids];b,c,d=b/a,c/a,d/a;v=Z(F(3,10))
 # Initial v is truly local order q-2 on its diagonal: the sole residual there must not vanish at v.
 f=FF(m+2,1)[0](v)[0].v;assert f.lo*f.hi>0
 def run(rad):
  z=[Z(V(q-rad,q+rad),[int(i==j) for j in range(2)]) for i,q in enumerate(cs)]
  return calc(m,v,*z,b,c,d)
 resid,_,_=run(0);enc,h,k=run(rad)
 B0=S.Matrix([[mid(t) for t in row.g] for row in resid]).inv();B=[[V(F(B0[i,j])) for j in range(2)] for i in range(2)]
 dis=max(norm(sum((t*r.v for t,r in zip(row,resid)),V(0))) for row in B)
 lip=max(sum(norm(V(int(i==j))-sum((t*r.g[j] for t,r in zip(row,enc)),V(0))) for j in range(2)) for i,row in enumerate(B))
 assert lip<F(1,3) and dis/(1-lip)<F(1,10**80)
 print(m,n,'displacement/radius',float(dis/rad),'Lipschitz',float(lip),'h,k',float(mid(h.v)),float(mid(k.v)),flush=True)


```

The following ES2020 script is standalone. Run with Node. It reconstructs the actual canonical order-eight input, the first fourteen paid forward states, all twelve actual old reverse rows and their independently transported upper effects, the new and genuinely self-tapped midpoint, the three final full representatives and the three literal 30-slot contractions. It uses the preceding forward enclosure, not a rounded optimum, for the two algebraic parameters. The proof of equality, rather than interval containment, is in the accompanying main note.

```javascript
const D=1n<<850n; const fl=(a,b)=>{if(b<0n){a=-a;b=-b}let q=a/b;return a<0n&&a%b?q-1n:q}; const ce=(a,b)=>-fl(-a,b);
class X{constructor(l,h){this.l=l;this.h=h}}const xi=(a=0,b=1)=>new X(fl(BigInt(a)*D,BigInt(b)),ce(BigInt(a)*D,BigInt(b)));const nr=s=>{let k=s.toString();if(k.includes('e'))throw Error(k);let a=k.split('.');return xi(a.join(''),10n**BigInt(a[1]?.length||0))};const X0=xi(),X1=xi(1);const plus=(a,b)=>new X(a.l+b.l,a.h+b.h),neg=a=>new X(-a.h,-a.l),sub=(a,b)=>plus(a,neg(b));const xm=(a,b)=>{let p=[a.l*b.l,a.l*b.h,a.h*b.l,a.h*b.h];return new X(fl(p.reduce((a,b)=>a<b?a:b),D),ce(p.reduce((a,b)=>a>b?a:b),D))}; const xd=(a,b)=>{if(b.l*b.h<=0n)throw Error("div0 "+xs(b));return xm(a,new X(fl(D*D,b.h),ce(D*D,b.l)))};const sg=a=>a.l>0n?1:a.h<0n?-1:0;const num=b=>Number(b)/Number(D);const mid=a=>(num(a.l)+num(a.h))/2;const xs=a=>[num(a.l),num(a.h)];const xrr=(n,f)=>Array.from({length:n},(_,i)=>f(i)),rs=(a)=>a.reduce(plus,X0),dt=(a,b)=>rs(a.map((v,i)=>xm(v,b[i])));const ev=(P,t)=>P.reduceRight((a,v)=>plus(v,xm(a,t)),X0),Int=(P,t)=>xm(t,ev(P.map((v,i)=>xd(v,xi(i+1))),t));const xpow=(a,n)=>n?xm(xpow(xm(a,a),n>>1),n&1?a:X1):X1;const comb=(n,k)=>{if(k<0||k>n)return 0n;let a=1n;for(let i=1;i<=k;i++)a=a*BigInt(n-i+1)/BigInt(i);return a};
const jco=n=>xrr(n+1,k=>xi((n-k)%2?-comb(n+1,k+1)*comb(n+2+k,k):comb(n+1,k+1)*comb(n+2+k,k)));
const T=(a,b)=>new X(a,b),must=(ok,msg)=>{if(!ok)throw Error(msg)};
const bis=(f,left,right,n)=>{let a=left.l,b=right.h,aa=sg(f(T(a,a))),bb=sg(f(T(b,b)));must(aa*bb==-1,"bracket");for(let j=0;j<n;j++){let m=(a+b)>>1n,ss=sg(f(T(m,m)));if(!ss)break;if(ss==aa)a=m;else b=m}must(sg(f(T(a,a)))*sg(f(T(b,b)))==-1,"final signs");return T(a,b)};
const rr=xrr,rg=n=>rr(n,i=>i),zeros=n=>rr(n,i=>X0),unit=(i,n)=>rr(n,j=>j==i?X1:X0),pad=(r,n)=>rr(n,i=>r[i]??X0),tr=A=>A[0].map((_,j)=>A.map(r=>r[j])),add=(r,v,k=X1)=>r.map((u,i)=>plus(u,xm(k,v[i]))),scale=(r,a)=>r.map(x=>xm(x,a)),lin=(v,R)=>tr(R).map(c=>dt(c,v)),mom=(x,n,k=0)=>rr(n,i=>xd(xpow(x,i+k+1),xi(i+k+1))),E=(x,n)=>rr(n,i=>xpow(x,i)),mm=(A,x)=>A.map(r=>dt(r,x));
function sol(M,v){let A=M.map((r,i)=>[...r,v[i]]),n=v.length;for(let j=0;j<n;j++){let a=-1;for(let i=j;i<n;i++)if(sg(A[i][j])&&(a<0||Math.abs(mid(A[i][j]))>Math.abs(mid(A[a][j]))))a=i;must(a>=0,"singular solve");[A[j],A[a]]=[A[a],A[j]];let p=A[j][j];A[j]=A[j].map(x=>xd(x,p));for(let i=0;i<n;i++)if(i!=j){let k=neg(A[i][j]);A[i]=add(A[i],A[j],k)}}return A.map(r=>r[n])}
const combRows=(P,R,v)=>lin(sol(tr(P),v),R),Pm=(p,q)=>{let r=zeros(p.length+q.length-1);p.forEach((a,i)=>q.forEach((b,j)=>r[i+j]=plus(r[i+j],xm(a,b))));return r},nod=V=>V.reduce((p,x)=>Pm(p,[neg(x),X1]),[X1]),inte=(p,x,k=0)=>dt(p,mom(x,p.length,k)),mz=(u,tol=100)=>!sg(u)&&(u.h-u.l)*10n**BigInt(tol)<D,cb=(x,a,b)=>x.l>=nr(a).l&&x.h<=nr(b).h;
function det3(M){let ss=(i,j)=>sub(xm(M[1][i],M[2][j]),xm(M[1][j],M[2][i]));return plus(sub(xm(M[0][0],ss(1,2)),xm(M[0][1],ss(0,2))),xm(M[0][2],ss(0,1)))}
function p8(){let l=bis(t=>ev(jco(3),t),nr(".171"),nr(".174"),650),g=[X0,l,xi(1,2),sub(X1,l),X1];let w=sol(tr(g.map(z=>E(z,5))),mom(X1,5)),y=g.slice(0,3),R=[[X0,X0,X0],[xd(l,xi(2)),xd(l,xi(2)),X0],sol(tr(y.map(z=>E(z,3))),mom(y[2],3))];let br=z=>sol(tr(y.map(z=>E(z,3))),mom(z,3)),a=l,v=sub(X1,l),G=[[X0],[xd(a,xi(4)),xd(a,xi(4))],[X0,a,X0],[xd(a,xi(6)),xd(xm(xi(2),a),xi(3)),xd(a,xi(6)),X0]].map(r=>pad(r,5)),P=[E(X0,4),E(a,4),mom(a,4),E(v,4)],U=[unit(0,5),unit(3,5),G[3],unit(4,5)],pr=z=>combRows(P,U,mom(z,4)),pe=z=>combRows(P,U,E(z,4));G.push(pr(v));let idx=[0,1,2,1,3,4],ww=idx.map(i=>xd(w[i],xi(idx.filter(j=>j==i).length))),L=R.map(r=>pad(r,6));for(let k=3;k<6;k++){let j=idx[k],S=br(g[j]).map((x,h)=>xd(sub(xm(w[j],x),rs(R.map((r,l)=>idx[l]==j?xm(ww[l],r[h]):X0))),ww[k]));L.push(pad(S,6))}let T=rr(6,i=>rr(6,j=>xd(xm(ww[5-j],L[5-j][5-i]),ww[5-i]))),xx=idx.map(j=>sub(X1,g[j])).reverse(),A=[...G.map(r=>pad(r,11)),...T.map((r,i)=>[...add(pr(xx[i]),lin(r,xx.map(pe)),xi(-1)),...r])],B=[...zeros(5),...ww.reverse()];for(let [i,j] of [[5,0],[6,3],[7,4]]){for(let l=0;l<11;l++)must(mz(sub(A[i][l],A[j][l])),"seed merger");for(let row of A)row[j]=plus(row[j],row[i]);B[j]=plus(B[j],B[i])}let K=[0,1,2,3,4,8,9,10];return [K.map(i=>K.map(j=>A[i][j])),K.map(i=>B[i])]}
function kernel(M){let A=M.map(v=>v.slice()),m=A.length,n=A[0].length,js=[],ii=0;for(let j=0;j<n&&ii<m;j++){let i=ii;for(let k=ii;k<m;k++)if(Math.abs(mid(A[k][j]))>Math.abs(mid(A[i][j])))i=k;if(!sg(A[i][j]))continue;[A[ii],A[i]]=[A[i],A[ii]];let v=A[ii][j];A[ii]=A[ii].map(t=>xd(t,v));for(let k=0;k<m;k++)if(k!=ii)A[k]=add(A[k],A[ii],neg(A[k][j]));js.push(j);ii++}must(ii==m,"kernel rank");return rg(n).filter(j=>!js.includes(j)).map(j=>{let r=unit(j,n);js.forEach((q,i)=>r[q]=neg(A[i][j]));return r})}
function cm(z,L,n,op=E){return lin(L,z.map(t=>op(t,n)))}const eu=(x,L,z,n,op=E)=>add(op(x,n),cm(z,L,n,op),xi(-1)),grab=(a,i)=>i.map(j=>a[j]),vt=(a,n)=>a.slice(0,n),act=(p,W)=>W.map(v=>dt(v,p));
function rcore(c){let w=sol(tr(c.map(z=>E(z,5))),mom(X1,5)),z=c.slice(1,-1).reverse().map(t=>sub(X1,t)),h=z.map(t=>sub(X1,t)),ww=w.slice().reverse().slice(0,4),D=ww.slice(1),pairs=rg(3).flatMap(i=>rg(i+1).map(j=>[i,j])),M=rg(3).map(v=>pairs.map(([i,j])=>i==v?z[j]:X0)),b=z.map(t=>xd(xpow(t,2),xi(2)));for(let v of [1,2]){M.push(pairs.map(([i,j])=>j==v?xm(D[i],h[i]):X0));b.push(xd(xm(D[v],xpow(h[v],2)),xi(2)))}M.push(pairs.map(([i,j])=>xm(D[i],xm(xpow(h[i],2),xpow(z[j],2)))));b.push(rs(D.map((w,i)=>xd(xm(w,xm(xpow(h[i],2),xpow(z[i],3))),xi(3)))));let a=sol(M,b),L=rr(4,i=>zeros(4));pairs.forEach(([i,j],k)=>L[i+1][j+1]=a[k]);for(let i=1;i<4;i++)L[i][0]=sub(z[i-1],rs(L[i]));let A=rr(5,i=>zeros(9));for(let i=1;i<5;i++){for(let j=1;j<5;j++)A[i][j]=xd(xm(L[4-j][4-i],ww[4-j]),ww[4-i]);A[i][0]=sub(c[i],rs(A[i]))}A.push(add(scale(pad(w,9),xi(2)),A[4],xi(-1)));return [A,w]}
function head(){let bounds=[[49,52],[160,163],[317,320],[],[680,683],[837,840],[948,951]],Y=bounds.map(z=>z.length?bis(t=>ev(jco(7),t),xi(z[0],1000),xi(z[1],1000),500):xi(1,2)),u=Y[5],r=Y[6],s=Y[0],Z1=Y[6],Z2=Y[4],Z3=Y[5],z0=[X0,Y[1],Y[3],Y[5],X1], [A,w]=rcore(z0),z=[...z0,X1],h=A.map((row,i)=>sub(dt(row.slice(0,6),z.map(v=>xpow(v,2))),xd(xpow(z[i],3),xi(3)))),m=scale(add(unit(4,9),unit(5,9)),xi(1,2)),U=pad(w,9),U1=pad(prox(w,z0),9),raw=[unit(0,9),m,U,U1],Q=n=>[E(X0,n),E(X1,n)],W5=n=>[...Q(n),mom(X1,n)],W4=n=>[...W5(n),mom(X1,n,1)],L=scale(unit(3,6),xi(1,4));function row(t,L,z,B,Br,n){let DF=eu(t,L,z,n,E),DI=eu(t,L,z,n,mom),K=kernel(B),g=xd(dt(DI,K[0]),dt(DF,K[0])),Zc=sol(tr(B.map(v=>vt(v,B.length))),vt(add(DI,DF,neg(g)),B.length)),ZZ=lin(Zc,Br),R=add(add(lin(L,A),ZZ),pad(L,9),neg(g));R[A.length]=g;A.push(R);return add(unit(A.length-1,9),pad(L,9),xi(-1))}
const Fu=n=>eu(u,L,z,n,E),Ru=row(u,L,z,W4(5),raw,5),WW=n=>[...W5(n),Fu(n)],RR=[...raw.slice(0,3),Ru];let za=[...z,u],ha=[...h,dt(L,h)],ps=kernel([...Q(7),mom(Z1,7),E(Z1,7),E(Z2,7),mom(Z2,7)])[0],M=rg(3).map(k=>za.map((t,i)=>xm(sub(t,r),xm(ha[i],xpow(t,k)))));M.push(za.map(t=>ev(ps,t)));let bb=[X0,X0,X0,ev(ps,r)],ids=[4,1,2,3],piv=M.map(r=>grab(r,ids)),base=zeros(7),slp=unit(6,7),bt=sol(piv,bb),st=sol(piv,M.map(r=>neg(r[6])));ids.forEach((j,i)=>{base[j]=bt[i];slp[j]=st[i]});let K=kernel(WW(6)),Aa=act(eu(r,base,za,6,mom),K),Ba=act(scale(cm(za,slp,6,mom),xi(-1)),K),Cc=act(eu(r,base,za,6,E),K),Dd=act(scale(cm(za,slp,6,E),xi(-1)),K),dt2=(u,v)=>sub(xm(u[0],v[1]),xm(u[1],v[0])),poly=[dt2(Aa,Cc),plus(dt2(Ba,Cc),dt2(Aa,Dd)),dt2(Ba,Dd)],q=bis(t=>ev(poly,t),xi(-8),xi(-7),350),Lr=add(base,slp,q),Fr=n=>eu(r,Lr,za,n),Rr=row(r,Lr,za,WW(6),RR,6);let z8=[...za,r],h8=[...ha,dt(Lr,ha)],T0=kernel([...Q(7),Fr(7),E(Z1,7),mom(Z1,7)]),Ms=[...rg(3).map(k=>z8.map((v,i)=>xm(sub(v,s),xm(h8[i],xpow(v,k))))),...T0.map(p=>z8.map(t=>ev(p,t)))],bs=[X0,X0,X0,...T0.map(p=>ev(p,s))],ix=[1,2,3,4,6],Ls=zeros(8),cs=sol(Ms.map(r=>grab(r,ix)),bs);ix.forEach((j,i)=>Ls[j]=cs[i]);let fs=row(s,Ls,z8,[...WW(6),Fr(6)],[...RR,Rr],6);return {A,c:[...z8,s],q,Y,RI:[Rr,fs],F:I=>[Fr(I),eu(s,Ls,z8,I,E)]}}
function prox(x,y){return x.map((v,i)=>xm(v,y[i]))}
function rcheck(){let {A,c,q}=head(),z=[{u:c.map(()=>X1),name:""}],ds=[];for(let j=0;j<=7;j++){let zz=[];for(let v of z){let err=add(v.u,c.map(t=>xpow(t,j)),xi(-1));ds.push({v:err.slice(1),name:v.name});if(j<7)zz.push({u:prox(v.u,c),name:v.name+"C"},{u:scale(mm(A,v.u),xi(j+1)),name:v.name+"A"})}z=zz}
const selected=[];let M=[];for(let {v,name} of ds){let vv=v.slice();for(let {i,r} of M)vv=add(vv,r,neg(vv[i]));let j=vv.findIndex(t=>sg(t));if(j<0)continue;let d=vv[j];M.push({i:j,r:vv.map(t=>xd(t,d))});selected.push(name);if(M.length==8)break}return {selected,rank:M.length,q:mid(q)}}
function forwardThree(Y){
  const a=sub(X1,Y[0]), b=xd(sub(X1,Y[1]),a), c=xd(sub(X1,Y[2]),a);
  const v=xi(3,10),eps=xi(1,10n**80n);
  const box=s=>{let x=nr(s);return T(x.l-eps.h,x.h+eps.h)};
  const r=box(".977805897551902537853703311306170191685702032435997116498430429947247888152481379996063");
  const s=box("-.458224610015433205871080595712990749276174198339611828714810304412624468841399015909507");
  const [A0,beta]=p8(),A=A0.map(v=>pad(v,14)), clock=A.map(rs),eye=i=>unit(i,14);
  const W=n=>[E(X0,n),E(X1,n),...rg(9-n).map(j=>mom(X1,n,j))];
  const B=n=>[eye(0),eye(8),...rg(9-n).map(j=>pad(beta.map((q,i)=>xm(q,xpow(clock[i],j))),14))];
  A.push(pad(beta,14));
  A.push(combRows([...W(6),E(v,6)],[...B(6),eye(9)],mom(v,6)));
  let low=[...W(7),E(v,7),mom(v,7),E(r,7)],lowB=[...B(7),eye(9),A[9],eye(10)];
  let hrow=sol(tr(low),mom(r,7)),h=hrow[low.length-2];A.push(lin(hrow,lowB));
  const Br=add(E(r,8),E(v,8),neg(h)),br=add(eye(10),eye(9),neg(h)),ub=[...W(8),Br,E(s,8),E(v,8),E(b,8),E(c,8)];
  let uu=sol(tr(ub),mom(c,8)),kk=neg(xd(uu[5],uu[4])),Bs=add(E(s,8),E(v,8),neg(kk)),bs=add(eye(11),eye(9),neg(kk));
  const lp=[...W(7),E(v,7),E(r,7),E(s,7)],lb=[...B(7),eye(9),eye(10),eye(11)];
  A.push(add(combRows(lp,lb,add(mom(s,7),mom(v,7),neg(kk))),A[9],kk));
  let hi=[...W(8),Br,Bs,E(b,8)],hb=[...B(8),br,bs,eye(12)];
  for(let [j,at] of [[12,b],[13,c]]){
   if(j==13){hi.push(E(c,8));hb.push(eye(13))}
   let n=hi.length,cp=sol(tr(hi.map(v=>v.slice(0,n))),mom(at,n));
   for(let k=n;k<8;k++)must(mz(sub(dt(cp,hi.map(v=>v[k])),mom(at,8)[k]),15),"upper flag");
   A.push(lin(cp,hb));}
  let pp=[E(X0,8),E(X1,8),E(b,8),E(c,8),mom(X1,8),mom(b,8),mom(c,8),mom(X1,8,1)];
  let rp=[eye(0),eye(8),eye(12),eye(13),A[8],A[12],A[13],B(7)[3]];
  const Pi=rg(8).map(i=>combRows(pp,rp,unit(i,8)));
  return {A,Pi,a};
}
function hermite(){
 let {A,c:z,Y,q,RI,F}=head(),N=16;A=A.map(r=>pad(r,N));const front=forwardThree(Y);
{
 const f=front,A=f.A,u=f.a,cc=A.map(rs),marks=[8,12,13],t=[],sizes=[],av=[],e0=unit(0,14);let mx=0;
 for(let k=1;k<=8;k++){
  let cnt=sizes.length;function gen(rem,idx,kids){if(!rem){let v=cc.map((c,i)=>kids.reduce((h,j)=>xm(h,av[j][i]),X1));
   for(let i of marks){let er=sub(dt(A[i],v),xd(xpow(cc[i],k),xi(k)));must(mz(er,34),"actual input to solid marks");mx=Math.max(mx,Math.max(...xs(er).map(Math.abs)))}
   if(k<=7){for(let k0=0;k0<8;k0++)must(mz(sub(dt(f.Pi[k0],v),xi(+(k0==k-1))),34),"lower projection")}
   sizes.push(k);av.push(scale(mm(A,v),xi(k)));return}
  for(let j=idx;j<cnt&&sizes[j]<=rem;j++)gen(rem-sizes[j],j,[...kids,j]);}gen(k-1,0,[]);
 }console.log("solid forward three",sizes.length,mx);
}
 const x=j=>sub(X1,Y[j]),node=[X0,...Y,X1],w=sol(tr(node.map(x=>E(x,9))),mom(X1,9));
 const refidx=[6,4,5],U=refidx.map(i=>Y[i]),lab=[-1,1,3,5,7,7,5,6,0];
 const truths=[E(X0,7),E(X1,7),...F(7)],raw=[unit(0,N),scale(add(unit(4,N),unit(5,N)),xi(1,2)),...RI.map(v=>pad(v,N))],means=[],ins=[];
  function insert(j,B,g) {
  let idx=A.length,prior=rg(idx).filter(i=>lab[i]==j),u=xi(1,prior.length+1);
  let M=scale(prior.concat(idx).map(i=>unit(i,N)).reduce((a,v)=>add(a,v),zeros(N)),u);
  let inc=add(B,M,g),R=scale(inc,xi(prior.length+1));for(let i of prior)R=add(R,A[i],xi(-1));
  A.push(R);z.push(Y[j]);lab.push(j);must(mz(sub(rs(R),Y[j]),34),"receiver clock");return [M,inc]
 }
 for(let l=0;l<3;l++){
  let r=U[l],basis=[...truths,E(r,7)],nn=basis.length,co=sol(tr(basis.map(v=>v.slice(0,nn))),mom(r,nn));
  for(let j=nn;j<7;j++)must(mz(sub(dt(co,basis.map(v=>v[j])),mom(r,7)[j]),55),"old gate");
  let [M,D]=insert(refidx[l],lin(co.slice(0,-1),raw),co[nn-1]);truths.push(E(r,7));raw.push(M);means.push(M);ins.push(D);
 }
 let G=nod([X0,x(0),x(1),x(2)]),P=Pm(G,G),H=P.slice(1).map((a,i)=>xm(xi(i+1),a));
 let alpha=refidx.concat(3).map(i=>xm(w[i+1],ev(H,x(i))));
 let gamma=refidx.concat(3).map(i=>xm(w[i+1],ev(P,x(i))));
 const prev=add(scale(unit(0,N),xm(w[0],ev(P,X1))),lin(gamma.slice(0,3),means));
 const B=scale(add(prev,lin(alpha.slice(0,3),ins),xi(-1)),xd(X1,alpha[3]));const sigma=xd(gamma[3],alpha[3]);
 let [M,D]=insert(3,B,sigma);means.push(M);ins.push(D);
 for(let i of [2,1,0])insert(i,combRows(truths,raw,mom(Y[i],7)),X0);
 let agg=lin(alpha,ins),La=lin(alpha,refidx.concat(3).map(i=>mom(Y[i],8))),queue=[rr(N,i=>X1)],nw=0;
 for(let j=0;j<=7;j++){let ne=[];for(let v of queue){nw++;
   must(mz(sub(dt(agg,v),La[j]),50),"weighted actual upper");
   for(let s of rg(7)){let ix=rg(N).filter(i=>lab[i]==s);let mv=xd(rs(ix.map(i=>v[i])),xi(ix.length));must(mz(sub(mv,xpow(Y[s],j)),50),"all means")}
   if(j<7)ne.push(prox(v,z),scale(mm(A,v),xi(j+1)));}queue=ne;}
 console.log("seven-length reverse words",nw,"actual causal diagonal",xs(sigma),"pure rank",rcheck());
 return {A,z,weights:lab.map(k=>xd(w[k+1],xi(lab.filter(i=>i==k).length))),front};
}
function ordinary(Q,upto=10){let {A:L,z,weights:w,front}=Q, n=L.length,m=front.A.length,{a,Pi}=front;const y=z.slice().reverse(),x=y.map(t=>sub(X1,t)),b=[...zeros(m),...w.slice().reverse()],pe=x.map(t=>lin(E(xd(t,a),8),Pi)),pj=x.map(t=>scale(lin(mom(xd(t,a),8),Pi),a)),T=rr(n,i=>rr(n,j=>xd(xm(w[n-1-j],L[n-1-j][n-1-i]),w[n-1-i]))),A=[...front.A.map(v=>pad(scale(v,a),m+n)),...T.map((row,i)=>[...add(pj[i],lin(row,pe),xi(-1)),...row])];let tags=[[0,8],[1,12],[2,13]].map(([i,j])=>[m+i,j]);for(let [i,j] of tags){for(let k=0;k<m+n;k++)must(mz(sub(A[i][k],A[j][k]),45),"literal whole row");for(let q of A)q[j]=plus(q[j],q[i]);b[j]=plus(b[j],b[i]);}let use=rg(m+n).filter(k=>!tags.some(([i,j])=>k==i));let M=use.map(i=>use.map(j=>A[i][j])),c=M.map(rs),B=use.map(i=>b[i]),s=M.length;must(s==27,"real stage count");for(let i=0;i<s;i++)for(let j=i+1;j<s;j++)must(M[i][j].l===0n&&M[i][j].h===0n,"triangular after transfers");
const sizes=[],avs=[],layers=[],par=[],mden=10n**42n;let mx=0n;for(let order=1;order<=upto;order++){let end=sizes.length,count=0;function rec(n,lo,kids){if(n==0){const v=c.map((_,j)=>kids.reduce((a,t)=>xm(a,avs[t][j]),X1)),res=sub(dt(B,v),xi(1,order));must(!sg(res),"signed ordinary condition");const bd=res.h>-res.l?res.h:-res.l;if(bd>mx)mx=bd;sizes.push(order);par.push(kids);if(order<upto)avs.push(scale(mm(M,v),xi(order)));count++;return;}for(let i=lo;i<end&&sizes[i]<=n;i++)rec(n-sizes[i],i,[...kids,i])}rec(order-1,0,[]);layers.push(count)}must(mx*mden<D,"alltree enclosures wide");console.log(JSON.stringify({order:upto,trees:sizes.length,layers,maxApprox:num(mx),stages:s}));return {M,c,B}}
const result=ordinary(hermite(),10);
```

Optional all-tree physical run: append this ES2020 block to the previous one in the same process. All 376,464 order-through-sixteen conditions were checked in the originating run. The stage-residual diagnostics supplement rather than replace the exact all-tree argument.

```javascript
function everydayTrees(A,b,N=16){const B=850n,ar=rr, flo=fl,ceil=ce,chk=must,bi=BigInt,min=(a,b)=>a<b?a:b,max=(a,b)=>a>b?a:b,ab=a=>a<0n?-a:a;const P=352n,Ks=1n<<P,conv=1n<<(B-P),rn=q=>[flo(q.l,conv),ceil(q.h,conv)],O=[Ks,Ks],Z=[0n,0n],n=b.length,rc=A.map((r,i)=>r.slice(0,i+1).map(rn)),bc=b.map(rn),ct=ar(N+1,()=>0),want=[0,1,1,2,4,9,20,48,115,286,719,1842,4766,12486,32973,87811,235381],H=Math.floor((N-1)/2);let worst=0n;
function prod(a,b){let x,y;if(a[0]>=0n){if(b[0]>=0n){x=a[0]*b[0];y=a[1]*b[1]}else if(b[1]<=0n){x=a[1]*b[0];y=a[0]*b[1]}else{x=a[1]*b[0];y=a[1]*b[1]}}else if(a[1]<=0n){if(b[0]>=0n){x=a[0]*b[1];y=a[1]*b[0]}else if(b[1]<=0n){x=a[1]*b[1];y=a[0]*b[0]}else{x=a[0]*b[1];y=a[0]*b[0]}}else if(b[0]>=0n){x=a[0]*b[1];y=a[1]*b[1]}else if(b[1]<=0n){x=a[1]*b[0];y=a[0]*b[0]}else{x=min(a[0]*b[1],a[1]*b[0]);y=max(a[0]*b[0],a[1]*b[1])}return [x,y]}
function m(a,b){let [l,h]=prod(a,b);return [l>>P,-((-h)>>P)]}
function sp(a,v){let l=0n,h=0n;for(let i=0;i<a.length;i++){let q=prod(a[i],v[i]);l+=q[0];h+=q[1]}return [l>>P,-((-h)>>P)]}
const one=ar(n,()=>O),compose=(big,sm)=>big.map((a,i)=>m(a,sm[i])),prim=e=>rc.map(r=>sp(r,e));function check(e,D,d){let q=sp(bc,e),lo=flo(Ks,D),hi=ceil(Ks,D);chk(q[0]*D<=Ks&&q[1]*D>=Ks,'merged ordinary rooted tree '+d+' #'+ct[d]);worst=max(worst,max(ab(q[0]-hi),ab(q[1]-lo)));ct[d]++}
let small=[],forests=ar(H+1,()=>[]);for(let d=1;d<=H;d++){let fresh=[];function rec(k,idx,p,D){if(!k){let dd=bi(d)*D;check(p,dd,d);fresh.push({n:d,p:prim(p),D:dd});forests[d-1].push({p,D});return}for(let j=idx;j<small.length&&small[j].n<=k;j++){let n=small[j];rec(k-n.n,j,compose(p,n.p),D*n.D)}}rec(d-1,0,one,1n);small.push(...fresh)}
function forestsAtH(k,idx,p,D){if(!k){forests[H].push({p,D});return}for(let j=idx;j<small.length&&small[j].n<=k;j++){let n=small[j];forestsAtH(k-n.n,j,compose(p,n.p),D*n.D)}}forestsAtH(H,0,one,1n);
function ext(d,p,D){for(let k=0;k<=N-d-1;k++){for(let F of forests[k]){let e=k?compose(p,F.p):p,nn0=d+k+1,dd=bi(nn0)*D*F.D;check(e,dd,nn0);if(nn0<N)ext(nn0,prim(e),dd)}}}
for(let d=H+1;d<=N;d++){function rec(k,idx,p,D){if(!k){let dd=bi(d)*D;check(p,dd,d);if(d<N)ext(d,prim(p),dd);return}for(let j=idx;j<small.length&&small[j].n<=k;j++){let n=small[j];rec(k-n.n,j,compose(p,n.p),D*n.D)}}rec(d-1,0,one,1n)}
chk(ct.every((x,i)=>x==want[i]),'all ordinary nonplane tree counts '+ct);return {count:ct.reduce((a,b)=>a+b,0),byOrder:ct.slice(1),worst:worst.toString(2).length-Number(P)}}

console.log(everydayTrees(result.M,result.B,16));
```
