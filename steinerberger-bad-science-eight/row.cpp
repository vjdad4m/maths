#include <algorithm>
#include <array>
#include <numeric>
#include <iostream>
#include <cmath>
using namespace std;
int k, boundsq, maxq;
long long exceptional, checked;
array<int,8> w; array<bool,200> good;
void search(int j, int minval, int q) {
  if (j==8) {
    if(q<=boundsq || q>128*k || q>k*std::accumulate(w.begin(),w.end(),0)) return;
    checked++;
    array<int,128> p;
    for(int i=0;i<128;i++) {
      int v=w[0];
      for(int d=0;d<7;d++) v+= (i>>d&1)?-w[d+1]:w[d+1];
      p[i]=abs(v);
    }
    for(int t=0;t<200;t++) if(good[t]){
      int b=k*t; for(int a:p)b+=max(a-t,0);
      if(b>=q)good[t]=false;
    }
    nth_element(p.begin(),p.begin()+k,p.end(),greater<int>());
    int s=0; for(int i=0;i<k;i++) s+=p[i];
    if(q<=s){exceptional++;maxq=max(maxq,q);}
    return;
  }
  if(q+(8-j)*k*k<=boundsq) return;
  for(int v=minval;v<=k;v+=2){w[j]=v;search(j+1,v,q+v*v);}
}
int main(){
  for(k=1;k<39;k++){
    long long r=17*k+48; boundsq=r*r/100;
    good.fill(true); exceptional=checked=0;maxq=0;
    search(0,k%2,0);
    cout<<k<<" bound="<<boundsq<<" screened="<<checked<<" survivors="<<exceptional<<" max_survivor_squared="<<maxq<<" thresholds:"; for(int t=0;t<200;t++) if(good[t]) cout<<" "<<t; cout<<endl;
  }
}
