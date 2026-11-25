#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <string>
using namespace std;
using U=unsigned;
int main() {
 ios::sync_with_stdio(false); cin.tie(nullptr);
 string s; int count=0, tight=0, lhsMin=1000000; array<int, 16> byOrder{};
 while (getline(cin,s)) {
   int n=s.at(0)-63;
   if (n<2 || n>15 || (int)s.size()!=1+(n*(n-1)/2+5)/6) return 2;
   array<U,16> a{};
   for (int j=1,k=0;j<n;++j) for(int i=0;i<j;++i,++k)
     if (((s.at(1+k/6)-63)>>(5-k%6))&1)
       {a[i]|=1U<<j; a[j]|=1U<<i;}
   auto adj = [&](U p){U y=0;for (;p;p&=p-1)y|=a[countr_zero(p)];return y;};
   U full=(1U<<n)-1;
   int even=0;
   for (int i=0;i<n;++i) {
     U f=1U<<i, seen=f; int e=0;
     for(int d=0;f;++d){if(!(d%2))e+=popcount(f);f=adj(f)&~seen;seen|=f;}
     if(seen!=full)return 3;
     even=max(even,e);
   }
   int td=n, cd=n;
   for (U p=1;p<=full;++p){
     int k=popcount(p);
     if(k>=max(td,cd)) continue;
     U w=adj(p);
     if (w==full)td=min(td,k);
     if (k>=cd || (w|p)!=full) continue;
     U f=p&-p, reached=f;
     while(f){f=adj(f)&p&~reached;reached|=f;}
     if(reached==p)cd=k;
   }
   int L=n==2?2:n-cd;
   if (L*td<2*even) {
     cout<<"COUNTEREXAMPLE "<<s<<" n="<<n<<" L="<<L<<" td="<<td<<" E="<<even<<'\n';return 1;
   }
   ++count; ++byOrder[n]; tight+=L*td==2*even; lhsMin=min(lhsMin,L*td-2*even);
 }
 for(int n=2;n<16;++n) if(byOrder[n])cout<<"n="<<n<<" connected="<<byOrder[n]<<'\n';
 cout<<"checked="<<count<<" tight="<<tight<<" min_margin="<<lhsMin<<" counterexamples=0\n";
}
