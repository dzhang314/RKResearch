"""Four pegs, so the active fourth row supplies the decisive fifth nodal peg."""
from off_literal_projection import *
from extra_active import bezout
from gauss_separate import span_unit
from off8_fibers import cramer

def nodal_5(pegs,Aq,Bq):
 W=[CX.constant(1)]+[CX.constant(0)]*7
 Ns=[]
 for x in pegs:
  W=list(W)
  for j in range(1,8):W[j]=can(W[j]+x*W[j-1])
  Ns.append(list(W))
 V=bezout()
 Cc=[can(Aq*Aq),can(-2*Aq*Bq),can(Bq*Bq)]
 W=[can(sum(Cc[j]*(expr(F2(V[j][i].v)) if i<len(V[j]) else 0) for j in range(3))) for i in range(4)]
 E=[]
 for i in range(5):
  Pp=[can(sum(Lco[s]*Ns[i][s+j-i] for s in range(5) if s+j>=i)) for j in range(4)]
  Pp.append(can(sum(W[k]*Ns[i][k-i] for k in range(i,4))))
  E.append(Pp)
 @lru_cache(None)
 def det0(i,bits):
  if i==len(E):return CX.constant(1)
  sg=1;v=CX.constant(0)
  for j in range(len(E)):
   if bits&(1<<j):
    if E[i][j]:v+=sg*can(E[i][j]*det0(i+1,bits^(1<<j)))
    sg=-sg
  return can(v)
 return det0(0,31)

def vec_s(P):
 T={}
 for (i,j,k),v in parts(P).items():
  if v:
   assert not i
   T.setdefault(j,{})[k]=v
 out=[]
 for j in range(max(T,default=-1)+1):
  d=T.get(j,{})
  out.append([d.get(k,F2(0)) for k in range(max(d,default=-1)+1)])
 return out

def primitive_s(Q):
 A=vec_s(Q)
 T=[]
 for s0 in A:
  if not s0:continue
  T=gcdp(T,s0)
  if len(T)==1:return [F2(1)],Q
 assert T
 return T,can(sum(term(divp(v,T)[0],g)*s**j for j,v in enumerate(A) if v))

def at_x(Poly):
 n=Poly.degrees()[1]
 return can(sum((expr(v)*(1-g)**j*g**(n+k-j) for (i,j,k),v in parts(Poly).items()),CX.constant(0)))

@lru_cache(None)
def active_projection(f,slot,rear,ori,quiet_four):
 A,B,m,C,D,ha,hb,anc,off,hh,Aq,Bq,Dn,Nn,Qp,Pn,guards,sh=tail_profile(f,slot,rear,ori)
 Phi,*_=eqs(f,slot,rear,ori)
 if quiet_four:G=exact_g(at_x(Phi))
 else:
  p=nodal_5([g*expr(anc),1-g,1-g*expr(C),1-g*expr(D),g*s],term(Aq,g),term(Bq,g))
  cs,ps=primitive_s(Phi)
  ch,ph=primitive_s(p)
  G=mul(mul(cs,ch),exact_g(can(ps.resultant(ph,1))))
 A=mon(guarded(G,guards))
 print('active8 four peg diagonal',f,slot,rear,ori,quiet_four,len(A)-1,flush=True)
 return A

def split_gamma(G,Bq,sh):
 C=gcdp(G,Bq)
 D=mon(guarded(G,[Bq]))
 H=gcdp(D,sh)
 E=mon(guarded(D,[sh]))
 return ((C,'constant'),(H,'hole'),(E,'coprime'))

def modfields(G,Bq,sh,p0,t0):
 V=Bfield(nmod_poly([0,1],p0),p0,t0)
 for M,kind in split_gamma(G,Bq,sh):
  if len(M)<=1:continue
  Md=nmod_poly([int(V(x).x[0]) for x in M],p0)
  assert Md.degree()==len(M)-1 and Md.leading_coefficient()==1
  for J,_ in Md.factor()[1]:
   F=Bfield(J,p0,t0);gg=F(nmod_poly([0,1],p0))
   yield F,gg,kind

def eval_y(P,F,gg,s0):
 W={}
 for (i,j,k),v in parts(P).items():W[i]=W.get(i,F(0))+F(v)*gg**k*s0**j
 return trim([W.get(i,F(0)) for i in range(max(W,default=-1)+1)])
def eval_s(P,F,gg,y0):
 W={}
 for (i,j,k),v in parts(P).items():W[j]=W.get(j,F(0))+F(v)*gg**k*y0**i
 return trim([W.get(j,F(0)) for j in range(max(W,default=-1)+1)])

def hole_quadratic(F,g,pegs,r,n):
 pp=Pcoeff(F,r);nu=intp(F,pp)/ev(pp,r)
 Z=nodal(pegs);zr=ev(Z,r)
 M=[intp(F,Z,j)-nu*zr*r**j for j in range(2*n)]
 A=[[M[i+j] for j in range(n)] for i in range(n)]
 D=det(A);D.inv()
 return [v/(D*g**(n-i)) for i,v in enumerate(cramer(A,[-M[n+j] for j in range(n)]))]+[F(1)]

def other_nodes(F,g,aa,bb,pegs,kind):
 if kind=='hole':
  r=aa/bb
  return hole_quadratic(F,g,pegs,r,2),r
 rat=(kind=='coprime')
 assert bool(bb)==rat
 return missing(F,g,aa/g,-bb,pegs,3),None

def finish(F,gg,s0,Y,r,kind,quiet_four,Phi,Et,Ea,T0,A0,X):
 ph=eval_y(Phi,F,gg,s0)
 assert len(ph)<=1
 e=F(0) if not ph else ph[0]
 T=eval_y(Et,F,gg,s0);A=eval_y(Ea,F,gg,s0)
 def at(E,Y):return ev(E,Y)
 if Y:
  W=Nested(Y);y=W.gen()
  span_unit(W, W(e),ev(list(map(W,T)),y),ev(list(map(W,A)),y))
 if kind=='hole':
  w=r/gg
  span_unit(F,e,ev(eval_y(T0,F,gg,s0),w),ev(eval_y(A0,F,gg,s0),w))
 if not quiet_four:span_unit(F,e,at(T,X),at(A,X))

def verify_active(f,slot,rear,ori,q4,p,t):
 _,_,_,C,D,_,_,anc,off,hh,Aq,Bq,_,_,_,_,_,sh=tail_profile(f,slot,rear,ori)
 Phi,_,_,Et,Ea,T0,A0,*_=eqs(f,slot,rear,ori)
 G=active_projection(f,slot,rear,ori,q4)
 for F,gg,kind in modfields(G,Bq,sh,p,t):
  a,b=(ev(list(map(F,v)),gg) for v in (Aq,Bq))
  anc0,C0,D0=map(F,(anc,C,D))
  X,C1,D1=(1-gg)/gg,1/gg-C0,1/gg-D0
  known=[gg*v for v in (anc0,X,C1,D1)]
  Y,r=other_nodes(F,gg,a,b,known,kind)
  assert Y is not None
  if q4:finish(F,gg,X,Y,r,kind,q4,Phi,Et,Ea,T0,A0,X)
  else:
   U=Nested(Y);s=U.gen()
   Y,err=qr(list(map(U,Y)),[-s,U(1)]);assert not err
   finish(U,U(gg),s,Y,U(r) if r is not None else None,kind,q4,Phi,Et,Ea,T0,A0,U(X))
 return True
