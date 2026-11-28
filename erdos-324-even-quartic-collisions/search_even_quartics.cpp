#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <cstdint>
struct Pair { std::int64_t value; int a,b; };
int main(int argc,char** argv) {
 if(argc!=4) return 1;
 int lo=std::atoi(argv[1]),hi=std::atoi(argv[2]),n=std::atoi(argv[3]);
 if(n<1 || n>20000 || lo < -1000000 || hi > 1000000) return 2;
 std::vector<Pair> pairs; pairs.reserve(std::size_t(n)*(n+1)/2);
 for(int c=lo;c<=hi;++c){
  pairs.clear();
  std::vector<std::int64_t> f(n+1);
  for(std::int64_t i=0;i<=n;++i) f[i]=i*i*(i*i+c);
  for(int i=0;i<n;++i) for(int j=i+1;j<=n;++j)
   pairs.push_back({f[i]+f[j],i,j});
  std::sort(pairs.begin(),pairs.end(),[](Pair x,Pair y){return x.value<y.value;});
  auto it=std::adjacent_find(pairs.begin(),pairs.end(),[](Pair x,Pair y){return x.value==y.value;});
  std::cout << c;
  if(it==pairs.end()) std::cout << " none";
  else std::cout<<" "<<it->a<<" "<<it->b<<" "<<(it+1)->a<<" "<<(it+1)->b;
  std::cout<<std::endl;
 }
}
