"""Tail and quadrature tests in the fixed exact early diagonal bases."""
from nong_front import candidates
from gauss_separate import span_unit
from one_front_zero import *

def modsplit(f,slot,br,p,t):
 Y=candidates(f,slot,br)
 for r0,_ in nmod_poly(list(Lco),p).roots():
  V=Bfield(nmod_poly([-int(r0),1],p),p,t)
  cv=lambda e:int(V(e).x[0])
  Mp=nmod_poly(list(map(cv,Y)),p)
  assert Mp.degree()==len(Y)-1 and Mp.leading_coefficient()==1
  for G,_ in Mp.factor()[1]:
   W=Bfield(G,p,t);g=W(nmod_poly([0,1],p));r=W(int(r0))
   cast=lambda v:W(cv(v))
   yield W,g,r,cast

def star_scale(F,p,x,g):
 y=x-g
 return p[3]*g**3+g*g*(p[2]+3*p[3]*y)+ev(p,x)

def gap_polys(F,g,r,x,rear,quiet):
 u=[F(0),F(1)];k=[F(1),F(2),F(-1)]
 P=Pcoeff(F,r);C=[x,-g];D=[x-2*g,g] if rear else [x,-2*g]
 px=ev(P,x);pc=subst(P,C);pd=subst(P,D)
 if quiet:
  E=add(mul([F(-2),F(1)],pc),sc(add(sc(u,2),mul(k,[F(-2),F(1)])),-px))
  assert not E[0]
  return E[1:]
 H=[F(-2),F(1),F(4),F(-1)];T=[F(2),F(3),F(-12),F(4)]
 E=sum_poly([sc(mul(T,pc),2),mul(H,pd),sc(mul(k,T),-px)])
 assert not E[0]
 return E[1:]

def hankel_at(F,pegs):
 D=nodal(pegs);a,b,c=[intp(F,D,j) for j in range(3)]
 return a*c-b*b

def mod_u(f,slot,br,p,t):
 failures=[];ts=0
 for V,g,r,cv in modsplit(f,slot,br,p,t):
  ts+=1
  x=1-g;P=Pcoeff(V,r)
  a=g*cv(B0(Epoly(JJ(ends(f,1)[slot]))))
  if not x-r:failures.append('x=r')
  if not star_scale(V,P,x,g):failures.append('star singleton phase')
  E=gap_polys(V,g,r,x,False,False)
  if len(E)!=5:failures.append(('tail leading',len(E)-1))
  if len(E)<=1:continue
  T=Tower(mon(E));u=T.gen()
  g,x,r,a=map(T,(g,x,r,a)); c=x-g*u;d=x-2*g*u
  H=hankel_at(T,[a,x,c,d,r])
  if not conditional_zero(T,H):
   gg=gcdp(T.F,H.x)
   what=[]
   for j,dif in [('u',u),('k',1+2*u-u*u),('c=r',c-r),('d=r',d-r),
                  ('a=c',a-c),('a=d',a-d),('p(c)',Pphys(T,r,c)),('p(d)',Pphys(T,r,d))]:
    if len(gcdp(gg,dif.x))>1:what.append(j)
   failures.append(('arithmetic moment common',len(gg)-1,what))
 print('early resultant cheaper arcs',f,slot,br,p,ts,failures,flush=True)
 return failures
