#include <algorithm>
#include <array>
#include <iostream>
#include <cstdlib>
using namespace std;
int k, boundsq, maxq;
long long exceptional, checked;
array<int,7> w;
void search(int j, int minval, int q) {
  if (j==7) {
    if(q<=boundsq) return;
    checked++;
    array<int,64> p;
    for(int i=0;i<64;i++) {
      int v=w[0];
      for(int d=0;d<6;d++) v+= (i>>d&1)?-w[d+1]:w[d+1];
      p[i]=abs(v);
    }
    nth_element(p.begin(),p.begin()+k,p.end(),greater<int>());
    int s=0; for(int i=0;i<k;i++) s+=p[i];
    if(q<=s){exceptional++;maxq=max(maxq,q);}
    return;
  }
  if(q+(7-j)*k*k<=boundsq) return;
  for(int v=minval;v<=k;v+=2){w[j]=v;search(j+1,v,q+v*v);}
}
int main(){
  for(k=1;k<24;k++){
    if(k==8)boundsq=256;
    else if(k==16)boundsq=768;
    else {long long p=1464*k+4286; boundsq=p*p/1000000;}
    exceptional=checked=0;maxq=0;
    search(0,k%2,0);
    cout<<k<<" bound="<<boundsq<<" screened="<<checked<<" survivors="<<exceptional<<" max_survivor_squared="<<maxq<<endl;
  }
}
