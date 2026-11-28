"""Sole nonliteral silent eighth: actual ratio and ordinary fifth nodal gate."""
from star_67 import *
from arithmetic_crt import prep,bivar,degree_safe_reduction,red_coords
from time import perf_counter

def embed4(Z):
 # j5 nodal routine is already general; write the five-pegs Newton
 # determinant directly in the full y,s,u,g,t context.
 h=[CX.constant(1)]+[CX.constant(0)]*7
 hs=[]
 ps,q0,q1=Z
 for p in ps:
  h=list(h)
  for j in range(1,8):h[j]=fold(h[j]+p*h[j-1])
  hs.append(h)
 aa=ns.bezout()
 Bs=[fold(q0*q0),fold(2*q0*q1),fold(q1*q1)]
 B=[fold(sum(Bs[j]*C(aa[j][k]) for j in range(3) if k<len(aa[j]))) for k in range(4)]
 M=[]
 for i in range(5):
  z=hs[i]
  M.append([fold(sum(Lco[k]*z[k+j-i] for k in range(5) if k+j>=i))
            for j in range(4)]+[fold(sum(B[k]*z[k-i] for k in range(i,4)))])
 @lru_cache(None)
 def detm(i,mask):
  if not mask:return CX.constant(1)
  r=CX.constant(0);sg=1
  for j in range(5):
   if mask>>j&1:
    if M[i][j]:r+=sg*fold(M[i][j]*detm(i+1,mask^(1<<j)))
    sg=-sg
  return fold(r)
 return detm(0,(1<<5)-1)

@lru_cache(None)
def inputs8(f,i):
 J,T,A,D,Q0,P0,gs,a,b=front(f,i)
 X=1-g;C1=X-g*u
 q0,q1=coeff_var(Q0,0);q0=fold(g*q0);q=lambda z:fold(q0+q1*z)
 k=1+2*u-u*u
 E0=fold((u-2)*L(C1)*q(X)-(2*u+k*(u-2))*L(X)*q(C1))
 E0=exdiv(E0,u)
 safe=q_guards(Q0,gs,a)
 E,fe=guard_strip(E0,[u,u-2,k,*safe])
 st=perf_counter()
 N0=embed4(([g*a,g*s,X,C1,g*y],q0,q1))
 N,fn=guard_strip(N0,[u,u-2,k,*safe,y-a,y-s])
 print('j8 actual rear, nodal fifth',f,i,E.degrees(),N.degrees(),fe,fn,round(perf_counter()-st,3),flush=True)
 assert E.degrees()==(0,3,4,9,1) and N.degrees()==(3,5,3,17,1)
 st=perf_counter()
 P=fold(D.resultant(N,0))
 assert P and not P.degrees()[0]
 P,fp=guard_strip(P,[u,u-2,k,*safe])
 print('j8 first nodal y projection',f,i,P.degrees(),fp,round(perf_counter()-st,3),flush=True)
 assert P.degrees()==(0,24,9,51,1) and not any(fp)
 R=bivar(prep(E,P),(f,i,'j8'))
 assert R.degrees()==(0,123,0,285,1)
 R,fr=guard_strip(R,safe)
 assert R.degrees()==(0,87,0,171,1) and fr==[18,0,0,3,9,0,3,0,0,0,3]
 print('j8 exact rear-supported projection',f,i,R.degrees(),fr,flush=True)
 return J,R,T,A,D,Q0,E,N,P
