// Exact rational norm generator for the two-pair quadratic ERK10 mean chart.
// Build: g++ -O3 -std=c++17 quadratic_mean_norms.cpp -lgmpxx -lgmp
// Prints coefficient arrays, low-to-high, for the cleared seam and residue norms.
// Use replay_quadratic_mean.py to verify the full certificate.
#include <bits/stdc++.h>
#include <gmpxx.h>
using namespace std;

mpq_class inv(long a) { if(!a)throw runtime_error("zero nonunit");mpq_class r(1,a);r.canonicalize();return r; }
struct U{
 vector<mpq_class> v;
 U(long a=0){if(a)v.emplace_back(a);}
 U(mpq_class a){if(a!=0)v.push_back(a);}
 U(vector<mpq_class> a):v(move(a)){trim();}
 void trim(){while(v.size()&&v.back()==0)v.pop_back();}
 int deg()const{return (int)v.size()-1;}
 mpq_class at(int a)const{return a<0||a>=v.size()?mpq_class(0):v[a];}
 U operator+(const U &b) const{vector<mpq_class>c(max(v.size(),b.v.size()));for(int i=0;i<c.size();++i)c[i]=at(i)+b.at(i);return U(c);}
 U operator-(const U &b) const{vector<mpq_class>c(max(v.size(),b.v.size()));for(int i=0;i<c.size();++i)c[i]=at(i)-b.at(i);return U(c);}
 U operator-()const{return U()-*this;}
 U operator*(const U &b)const{
  if(v.empty()||b.v.empty())return U();
  vector<mpq_class>c(v.size()+b.v.size()-1);
  for(int i=0;i<v.size();++i)if(v[i]!=0)for(int j=0;j<b.v.size();++j)if(b.v[j]!=0)c[i+j]+=v[i]*b.v[j];
  return U(c);
 }
 bool operator==(const U& b)const{return v==b.v;}
};
template<int N,class V,int ID>struct Q{
 array<V,N> v;
 static array<V,N> mod;
 Q(int a=0){v[0]=V(a);}
 Q(mpq_class a){v[0]=V(a);}
 static Q embed(const V &a){Q r;r.v[0]=a;return r;}
 static Q x(){Q r;r.v[1]=V(1);return r;}
 Q operator+(const Q &b)const{Q c;for(int i=0;i<N;++i)c.v[i]=v[i]+b.v[i];return c;}
 Q operator-(const Q &b)const{Q c;for(int i=0;i<N;++i)c.v[i]=v[i]-b.v[i];return c;}
 Q operator-()const{return Q()-*this;}
 Q operator*(const Q &b)const{
  array<V,2*N-1>c;
  for(int i=0;i<N;++i)if(!(v[i]==V()))for(int j=0;j<N;++j)if(!(b.v[j]==V()))c[i+j]=c[i+j]+v[i]*b.v[j];
  for(int k=2*N-2;k>=N;--k) if(!(c[k]==V())) for(int j=0;j<N;++j)c[k-N+j]=c[k-N+j]-c[k]*mod[j];
  Q r;for(int i=0;i<N;++i)r.v[i]=c[i];return r;
 }
 bool operator==(const Q& b)const{return v==b.v;}
};
template<int N,class V,int ID>array<V,N>Q<N,V,ID>::mod;
using P4=Q<4,U,0>;
using Q3=Q<3,P4,1>;
template<class V> V powr(V a,int k){V b(1);while(k){if(k&1)b=b*a;a=a*a;k>>=1;}return b;}
template<class V>V divc(V a,int b){return a*V(inv(b));}
template<class V>V eval(const vector<V> &a,V x){V r;for(int i=(int)a.size()-1;i>=0;--i)r=r*x+a[i];return r;}
template<class V>vector<V> mul(const vector<V>&a,const vector<V>&b){vector<V>c(a.size()+b.size()-1);for(int i=0;i<a.size();++i)for(int j=0;j<b.size();++j)c[i+j]=c[i+j]+a[i]*b[j];return c;}
template<class V>vector<V> neg(const vector<V>&a){vector<V>c=a;for(auto &x:c)x=-x;return c;}
template<class V>vector<V> add(vector<V>a,const vector<V>&b){if(a.size()<b.size())a.resize(b.size());for(int i=0;i<b.size();++i)a[i]=a[i]+b[i];return a;}
template<class V>vector<V> scale(vector<V>a,V s){for(auto &x:a)x=x*s;return a;}
template<class V>vector<V> sub(vector<V>a,const vector<V>&b){return add(a,neg(b));}
template<class V>vector<V> hull(const vector<V>&roots){vector<V>a{V(1)};for(auto x:roots)a=mul(a,{-x,V(1)});return a;}
template<class V>vector<V> J(vector<V>a){vector<V>b{V()};for(int i=0;i<a.size();++i)b.push_back(divc(a[i],i+1));return b;}
template<class V>V integ(const vector<V>&a){V b;for(int i=0;i<a.size();++i)b=b+divc(a[i],i+1);return b;}
template<class V>V form(const vector<V>&a,const vector<V>&b){return integ(mul(a,b));}
int binom(int j,int i){int u=1;for(int k=0;k<i;++k)u=u*(j-k)/(k+1);return u;}
template<class V>vector<V> star(const vector<V>&a){vector<V>b(a.size());
 for(int i=0;i<a.size();++i)for(int j=i;j<a.size();++j)b[i]=b[i]+V((i%2?-1:1)*binom(j,i))*a[j];
 return b;
}
template<class V>vector<V> quotient(const vector<V>& a, V t){
 vector<V>b=a,c(a.size()-1);for(int i=(int)a.size()-1;i>0;--i){c[i-1]=b[i];b[i-1]=b[i-1]+t*b[i];}return c;
}
template<class V>vector<V> prem(vector<V>a,const vector<V>& b){
 for(int k=(int)a.size()-1;k>=(int)b.size()-1;--k){
  V z=a[k];for(int j=0;j<(int)b.size()-1;++j)a[k-((int)b.size()-1)+j]=a[k-((int)b.size()-1)+j]-z*b[j];
 }a.resize(b.size()-1);return a;
}
template<class V>V det(const vector<vector<V>> &a){
 int n=a.size();vector<int>p(n);iota(p.begin(),p.end(),0);
 V r;
 do{V v(1);int d=0;for(int i=0;i<n;++i){v=v*a[i][p[i]];for(int j=i+1;j<n;++j)d+=p[i]>p[j];}
 if(d%2)r=r-v;else r=r+v;
 }while(next_permutation(p.begin(),p.end()));return r;
}
template<int N,class V,int ID>V norm(Q<N,V,ID> a){
 vector<vector<V>> mat(N,vector<V>(N));
 auto x=Q<N,V,ID>::x();
 for(int j=0;j<N;++j){for(int i=0;i<N;++i)mat[i][j]=a.v[i];a=a*x;}
 return det(mat);
}
template<class V>vector<V> polyInterp(vector<V>ys){
  int N=ys.size();vector<V>a(N);
  for(int i=0;i<N;++i){vector<V>b{V(1)};int m=1;for(int j=0;j<N;++j)if(i!=j){b=mul(b,{V(-j),V(1)});m=m*(i-j);}
    for(int j=0;j<N;++j)a[j]=a[j]+divc(ys[i]*b[j],m);
  }return a;
}
template<class V>V res2(const vector<V>& f,const vector<V>&g){
 // Exact padded resultant of quadratic f and degree bound g.size()-1.
 int n=g.size()-1;V a=f[2], b=f[1],c=f[0],s=-b,p=a*c;
 vector<V>h(n+1);h[0]=V(2);if(n)h[1]=s;
 for(int i=2;i<=n;++i)h[i]=s*h[i-1]-p*h[i-2];
 V r;
 for(int i=0;i<=n;++i){
  r=r+g[i]*g[i]*powr(c,i)*powr(a,n-i);
  for(int j=i+1;j<=n;++j)r=r+g[i]*g[j]*powr(c,i)*powr(a,n-j)*h[j-i];
 }return r;
}
vector<Q3> R,S,QL,QR;Q3 p,q,t,tr;
struct Data{Q3 H,G,D,Lc,Rc;};
Data F(int xx,int ww){
 Q3 x(xx),w(ww);
 auto rightBase=hull<Q3>({tr,w});
 auto leftBase=hull<Q3>({t,x});
 auto Pleft=[&](Q3 y){
   auto hl=mul(leftBase,{-y,Q3(1)});
   return mul<Q3>({-p,Q3(1)},sub(scale(hl,R[0]),scale(R,hl[0])));
 };
 auto Pright=[&](Q3 z){
   auto hr=mul(rightBase,{-z,Q3(1)});
   return mul<Q3>({-q,Q3(1)},sub(scale(hr,eval(R,Q3(1))),scale(R,eval(hr,Q3(1)))));
 };
 auto BL=J(J(hull<Q3>({Q3(),t,p})));
 auto BR=star(J(J(hull<Q3>({Q3(),Q3(1)-tr,Q3(1)-q}))));
 auto PL0=Pleft(Q3()),PL1=sub(Pleft(Q3(1)),PL0);
 auto PR0=Pright(Q3()),PR1=sub(Pright(Q3(1)),PR0);
 Q3 lc=form(BR,PL1),ld=form(BR,PL0), rc=form(BL,PR1),rd=form(BL,PR0);
 auto PNL=sub(scale(PL0,lc),scale(PL1,ld));
 auto PNR=sub(scale(PR0,rc),scale(PR1,rd));
 Q3 H=form(J(PNL),PNR);
 auto g=hull<Q3>({Q3(),Q3(1),p,q});
 auto d4=hull<Q3>({t,x,w,tr});
 auto xg=mul<Q3>({Q3(),Q3(1)},g);
 Q3 I0=integ(g),I1=integ(xg);
 vector<Q3>JR{I1+R[1]*I0,I0};
 auto prod=mul(mul(mul(mul(JR,d4),{ld,lc}),{rd,rc}),{Q3(1)});
 auto s=prem(prod,R),hh=prem<Q3>({Q3(),Q3(-1),Q3(1)},R);
 Q3 G=s[0]*hh[1]-s[1]*hh[0];
 return {H,G,lc*rc,lc,rc};
}
void setup(){
 U d(vector<mpq_class>{0,1});
 vector<U>s4{U(inv(42))-d*U(inv(14)),U(-14*inv(42))+d*U(9*inv(14)), U(56*inv(42))+d*U(-21*inv(14)),U(-2)+d,U(1)};
 for(int i=0;i<4;++i)P4::mod[i]=s4[i];
 vector<P4>sp;for(auto u:s4)sp.push_back(P4::embed(u));
 auto pp=P4::x();
 auto q3=quotient(sp,pp);
 for(int i=0;i<3;++i)Q3::mod[i]=q3[i];
 vector<Q3>sq;for(auto u:q3)sq.push_back(Q3::embed(u));
 p=Q3::embed(pp);q=Q3::x();t=divc(p,2);tr=divc(Q3(1)+q,2);R=quotient(sq,q);
 auto prep=[&](vector<Q3> r,Q3 p){
   Q3 t=divc(p,2);Q3 h=eval(r,t);auto b=scale(r,powr(t,3));b.resize(4);b[2]=b[2]-h*p;b[3]=h;
   return quotient(b,t);
 };
 QL=prep(R,p); QR=star(prep(star(R),Q3(1)-q));
}

void print(const U&a){
 cout<<"["; for(int i=0;i<a.v.size();++i){if(i)cout<<",";cout<<"\""<<a.v[i]<<"\"";}cout<<"]\n";
}
int main(int argc,char** argv){
 setup();
 vector<int>tests{0,-1};
 if(argc>1)tests={stoi(argv[1])};
 for(int c:tests){
  vector<Q3>rv;
  for(int w=0;w<=4;++w){
   vector<Q3>vals;
   for(int x=0;x<3;++x){Data d=F(x,w);vals.push_back(c==-1?d.G:(d.H+Q3(c)*d.G));}
   auto f=polyInterp(vals);rv.push_back(res2(QL,f));
  }
  auto wr=polyInterp(rv);auto h=res2(QR,wr);
  U N=norm(norm(h));cout<<c<<" "<<N.deg()<<"\n";print(N);cout.flush();
 }
}
