/*
 * Content-compressed exact integer Gram verification (GMP, no tree enumeration).
 * stdin: stages order d e; row-major integer A numerator; integer b numerator.
 */
#include <gmpxx.h>
#include <iostream>
#include <vector>
#include <utility>
#include <stdexcept>
using Z = mpz_class;
using Row = std::vector<Z>;
using Mat = std::vector<Row>;
static Z gcdz(const Z&a,const Z&b){Z c;mpz_gcd(c.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return c;}
static Z extract(Mat& a){
    Z d=0;for (const auto&r:a)for(const auto& x:r){d=gcdz(d,x);if(d==1)break;}
    if(d==0)d=1;
    if(d!=1)for(auto&r:a)for(auto&x:r)x/=d;
    return d;
}
int main(){
    int s,p; Z d,e;
    if(!(std::cin>>s>>p>>d>>e)||s<1||p<1||d==0||e==0) return 2;
    const int n=s+1;
    Mat L(n, Row(n));Row weights(s);
    for(int i=0;i<s;i++)for(int j=0;j<s;j++)if(!(std::cin>>L[i][j]))return 2;
    for(auto&z:weights)if(!(std::cin>>z))return 2;
    L[s][s]=d;
    for(int i=0;i<s;i++){if(4*L[i][i]!=d)return 3;for(int j=i+1;j<s;j++)if(L[i][j]!=0)return 3;}
    std::vector<std::vector<std::pair<int,Z>>> nz(n);
    Row rowFactor(n);
    for(int i=0;i<n;i++){
        Z a;for(const auto&v:L[i])a=gcdz(a,v);
        rowFactor[i]=a==0?1:a;
        for(int j=0;j<n;j++)if(L[i][j]!=0)nz[i].emplace_back(j,L[i][j]/rowFactor[i]);
    }
    std::vector<Mat> C{Mat(n,Row(n,1))},T;
    Row scale{1},trans;
    for(int g=0;g<p;g++){
        if(g){
            Mat a(n,Row(n));Row coeff(g);Z common;
            for(int l=1;l<=g;l++){coeff[l-1]=scale[g-l]*scale[l-1]*trans[l-1];common=gcdz(common,coeff[l-1]);}
            for(int l=1;l<=g;l++){
                const Z mult=coeff[l-1]/common;
                for(int i=0;i<n;i++)for(int j=0;j<=i;j++){
                    Z x = C[g-l][i][j]*T[l-1][i][j];
                    if(i<s)x*=l;if(j<s)x*=l;
                    mpz_addmul(a[i][j].get_mpz_t(),x.get_mpz_t(),mult.get_mpz_t());
                }
            }
            for(int i=0;i<n;i++)for(int j=0;j<i;j++)a[j][i]=a[i][j];
            scale.push_back(common*extract(a));C.push_back(std::move(a));
        }
        Row w(n);for(int i=0;i<s;i++)w[i]=(g+1)*weights[i];w[s]=-e;
        Z energy;
        for(int i=0;i<n;i++)if(w[i]!=0)for(int j=0;j<n;j++)if(w[j]!=0)energy+=w[i]*C[g][i][j]*w[j];
        if(energy!=0){std::cerr<<"nonzero exact energy at order "<<g+1<<'\n';return 1;}
        if(g+1<p){
            Mat lc(n,Row(n)),res(n,Row(n));
            for(int i=0;i<n;i++)for(int j=0;j<n;j++)
                for(const auto&[k,a]:nz[i])
                    mpz_addmul(lc[i][j].get_mpz_t(),a.get_mpz_t(),C[g][k][j].get_mpz_t());
            for(int i=0;i<n;i++)for(int j=0;j<=i;j++){
                Z z;
                for(const auto&[k,a]:nz[j])mpz_addmul(z.get_mpz_t(),lc[i][k].get_mpz_t(),a.get_mpz_t());
                res[i][j]=res[j][i]=z*rowFactor[i]*rowFactor[j];
            }
            trans.push_back(extract(res));T.push_back(std::move(res));
        }
    }
    std::cout<<s<<" strict SDIRK stages; all integer Gram energies zero at orders 1-"<<p<<"; diagonal 1/4\n";
}
