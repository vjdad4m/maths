// Expects connected simple graph6 records (nauty geng -cq), 2 <= n <= 16.
#include <algorithm>
#include <cassert>
#include <iostream>
#include <map>
#include <string>
using namespace std;
int count(int x) { return __builtin_popcount((unsigned)x); }
int first(int x) { return __builtin_ctz((unsigned)x); }
int main() {
  string s;
  map<int, long long> num, eq258, eq259;
  while (cin >> s) {
    int n = s[0] - 63, all = (1 << n) - 1, a[16] = {}, k = 0;
    assert(2 <= n && n <= 16 && s.size() == 1 + (n*(n-1)/2+5)/6);
    for (int j=1; j<n; ++j) for (int i=0; i<j; ++i, ++k)
      if ((s[1+k/6]-63) >> (5-k%6) & 1) {
        a[i] |= 1<<j; a[j] |= 1<<i;
      }
    int E = 0, cd = n, t = n, ecc[16]={};
    for (int i=0; i<n; ++i) {
      int seen = 0, frontier = 1<<i, neven = 0; bool even = true;
      while (frontier) {
        if (even) neven += count(frontier);
        seen |= frontier;
        int next = 0;
        for (int q=frontier; q; q&=q-1) next |= a[first(q)];
        frontier = next & ~seen; even = !even; if(frontier) ++ecc[i];
      }
      assert(seen == all);
      E = max(E, neven);
    }
    for (int d=1; d<=all; ++d) {
      int dc = count(d);
      if (dc >= max(cd,t)) continue;
      int covered = 0;
      for (int q=d; q; q&=q-1) covered |= a[first(q)];
      if (covered == all) t = min(t, dc);
      if (dc >= cd || (covered|d) != all) continue;
      int seen = 0, frontier = d&-d;
      while (frontier) {
        seen |= frontier;
        int next = 0;
        for (int q=frontier; q; q&=q-1) next |= a[first(q)];
        frontier = next & d & ~seen;
      }
      if (seen == d) cd = dc;
    }
    int L = n == 2 ? 2 : n-cd;
    int B=0,NB=0,S=0,NS=0;
    int diam=*max_element(ecc,ecc+n);
    for (int i=0;i<n;++i) {
      if(ecc[i]==diam) {B|=1<<i; NB|=a[i];}
      if(count(a[i])==2){S|=1<<i; NS|=a[i];}
    }
    int X=count(NB&~B),Y=count(NS&~S);
    if(2*X>t*L || 2*Y>t*L) {
      cerr<<s<<" n="<<n<<" X260="<<X<<" X261="<<Y<<" t="<<t<<" L="<<L<<"\n"; return 1;
    }
    ++num[n]; eq258[n]+=2*X==t*L; eq259[n]+=2*Y==t*L;
  }
  for(auto [n,c]:num)cout<<n<<' '<<c<<' '<<eq258[n]<<' '<<eq259[n]<<endl;
}
