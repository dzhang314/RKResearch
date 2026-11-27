#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
const vector<int> primes = {7,11,13,17,19,23,29,31,37,41};
struct Rat { int n,d; array<int,10> z; };
struct Gate {
 int p; vector<int> inv; vector<unsigned char> poss;
 Gate(int u):p(u),inv(p),poss(p*p*p) {
  for(int a=1;a<p;a++) for(int b=1;b<p;b++) if(a*b%p==1){inv[a]=b;break;}
 }
 int M(long x) const {x%=p; return x<0?x+p:x;}
 bool pass(int a,int u,int v,int w) const {
  int ts[5]={a,u,v,w,M(-a)},hs[5]={},ls[5]={};
  int ds[5]={}, nd=0;
  for(int x:ts){if(find(ds,ds+nd,x)==ds+nd)ds[nd++]=x;}
  if(nd<3)return false;
  if(nd<5) {
   int c[6]={1};
   for(int i=0;i<nd;i++){
    for(int j=i+1;j>=0;j--) c[j]=M((j?c[j-1]:0)-ds[i]*c[j]);
   }
   for(int j=0;j+nd<5;j++){
    int s=0;
    for(int k=0;k<=nd;k++)if(!((j+k)%2))s+=c[k]*inv[j+k+1];
    if(M(s))return false;
   }
  }
  int f=M((a+1)*(a+1));
  int ku=M((1+2*u+4*a*u-2*a*a-u*u)*inv[f]);
  int kw=M((1-2*w-4*a*w-2*a*a-w*w)*inv[f]);
  for(int i=0;i<5;i++){
   int s2=0,prod=1;
   for(int j=0;j<5;j++)if(j!=i) {
    prod=M(prod*ts[j]);
    for(int k=j+1;k<5;k++)if(k!=i)s2+=ts[j]*ts[k];
   }
   hs[i]=M(inv[5]+s2*inv[3]+prod);
  }
  int l3=M((u-w)*hs[0]+ku*(w-a)*hs[1]);
  int l4=M((u+a)*hs[0]-2*a*ku*hs[1]);
  if(M(l3*hs[4]-kw*l4*hs[3]))return false;
  for(int i=0;i<5;i++){
   ls[i]=M((u-ts[i])*hs[0]+ku*(ts[i]-a)*hs[1]);
   if(!hs[i] && ls[i])return false;
  }
  if(nd==5){
   if(!hs[4])return false;
   int s=0;
   for(int i=0;i<5;i++)if(hs[i]){
    int D=1;
    for(int j=0;j<5;j++)if(i!=j)D=M(D*(ts[i]-ts[j]));
    s=M(s+ls[i]*ls[i]*inv[M(D*hs[i])]);
   }
   if(s)return false;
  }
  return true;
 }
 void fill(){
  for(int a=0;a<p-1;a++)for(int u=0;u<p;u++)if(a!=u)for(int w=0;w<p;w++)
   for(int v=0;v<p;v++)if(pass(a,u,v,w)){poss[(a*p+u)*p+w]=1;break;}
 }
 bool check(int a,int u,int w) const{return poss[(a*p+u)*p+w];}
};
bool smooth(int a) { a=abs(a);if(!a)return false;for(int p:{2,3,5})while(a%p==0)a/=p;return a==1; }
int main(int argc,char**argv){
 int H=argc>1?atoi(argv[1]):16; vector<Gate> gates;
 for(int p:primes){gates.emplace_back(p);gates.back().fill();cerr<<"gate "<<p<<" "<<accumulate(gates.back().poss.begin(),gates.back().poss.end(),0)<<"\n";}
 stable_sort(gates.begin(),gates.end(),[](auto &a,auto &b){
  double x=accumulate(a.poss.begin(),a.poss.end(),0)/(double)(a.p*a.p*a.p);
  double y=accumulate(b.poss.begin(),b.poss.end(),0)/(double)(b.p*b.p*b.p);return x<y;});
 auto see=[&](int n,int d){Rat t{n,d,{}};for(size_t i=0;i<gates.size();i++)t.z[i]=gates[i].M(n*gates[i].inv[d%gates[i].p]);return t;};
 vector<Rat> gamma,dx,ws;
 for(int d=1;d<=H;d++)if(smooth(d))for(int n=-3*H;n<=3*H;n++)if(gcd(n,d)==1){
  if(smooth(n)){
   if(abs(n)<=4*d && 2*n!=d)gamma.push_back(see(n,d));
   if(abs(n)<=5*d)dx.push_back(see(n,d));
  }
  if(abs(n)<=5*d)ws.push_back(see(n,d));
 }
 cerr<<"counts "<<gamma.size()<<" "<<dx.size()<<" "<<ws.size()<<" total "<< (1L*gamma.size()*dx.size()*ws.size()) <<"\n";
 long nSurv=0;
 for(auto &g:gamma)for(auto &t:dx){
  array<int,10> az,uz;
  for(size_t i=0;i<gates.size();i++) {
   az[i]=gates[i].M(2*g.z[i]-1);uz[i]=gates[i].M(az[i]+2*t.z[i]);
  }
  for(auto &w:ws){
   bool ok=true;
   for(size_t i=0;i<gates.size();i++)if(!gates[i].check(az[i],uz[i],w.z[i])){ok=false;break;}
   if(!ok)continue;
   nSurv++;
   cout<<g.n<<" "<<g.d<<" "<<t.n<<" "<<t.d<<" "<<w.n<<" "<<w.d<<"\n";
  }
 }
 cerr<<"survivors "<<nSurv<<"\n";
}
