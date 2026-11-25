# Graffiti.pc #450

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Applies to finite simple connected graphs on n>3 vertices, as requested. Let I be a maximum 2-independent set; by the catalogue convention G[I] has maximum degree **one**. For a set D, pN(D) is the number of vertices having exactly one neighbor in D. Denote leaves' neighbors (supports) by S, minimum-degree vertices by A, degree-two vertices by A2, and degree-at-least-three vertices by H3.

## #450: |I| ≤ |V∖S| + pN(A2) + pN(V∖H3)

Focus on selected supports. At most pN(A2)+pN(V∖H3) of them are already counted by those two private-neighbor sets (take their union). For each remaining support:
- If it has an excluded leaf, charge it to such a leaf. Different supports get distinct excluded leaves outside S.
- Otherwise all its leaves are selected, so there is exactly one and every other neighbor is excluded. The support has at least two neighbors of degree ≤2, because its leaf has degree 1 and the support is not counted by pN(V∖H3). Therefore it has at least one degree-two neighbor, and in fact at least two because it is not counted by pN(A2). Each of these degree-two neighbors is excluded. If one is a support w, its degree two gives it exactly one leaf and exactly one other neighbor (the selected support under consideration). Charge to that leaf, which belongs to the set counted by pN(A2). These leaves are distinct across the charged supports, and they are neither supports nor excluded leaves charged above: they are not supports because n>3, and their unique neighbor is w, which is excluded.
- For what remains, all the at least two excluded degree-two neighbors lie outside S. Counting incidences, each such excluded vertex is adjacent to at most two supports, so the number of remaining selected supports is at most the number of these excluded degree-two vertices. The latter are disjoint from the excluded leaves.

The charges to private-neighbor sets count at most pN(A2)+pN(V∖H3), and all other charges count at most |(V∖S)∖I|. Adding the selected vertices outside S proves the bound.

## Verification scope

Lean checks the arithmetic implications from the written counting arguments, not the graph-to-premise reasoning. The shared Lean file is below (Lean 4.19.0). An independent exhaustive check found no violations on all 273,189 connected unlabeled graphs of orders four through nine.

<details>
<summary>Arithmetic2Independent.lean</summary>

```lean
import Std
set_option warningAsError true
namespace Graffiti2Independent

theorem supportBound (chosenOut chosenSupp totalOut privateCount : Nat)
    (hOut : chosenOut ≤ totalOut)
    (hCharge : chosenSupp ≤ privateCount + (totalOut - chosenOut)) :
    chosenOut + chosenSupp ≤ totalOut + privateCount := by omega

theorem conjecture448a (n chosen h lo m p : Nat)
    (hSize : n = h + lo)
    (hPathCover : lo ≤ p + h + m)
    (hChosen : chosen ≤ lo ∨ chosen ≤ (n+1)/2) :
    chosen ≤ h+m+p := by omega

theorem conjecture449 (lo a b e : Nat) (hLo : b ≤ lo)
    (hCount : 2*a ≤ 2*b+e) :
    lo-b+a ≤ lo+e/2 := by omega

theorem privateCharge450 (chosenSupp selectedPrivate markedLeaves missedLeaves rest missedTwo p2 pLow : Nat)
    (hCount : chosenSupp = selectedPrivate + markedLeaves + missedLeaves + rest)
    (hPrivate : selectedPrivate + markedLeaves ≤ p2+pLow)
    (hTwo : 2*rest ≤ 2*missedTwo) :
    chosenSupp ≤ p2+pLow+missedLeaves+missedTwo := by omega

#print axioms conjecture448a
#print axioms conjecture449
#print axioms privateCharge450
end Graffiti2Independent
```

</details>

<details>
<summary>scan2Independent.cpp</summary>

```cpp
#include <iostream>
#include <string>
#include <algorithm>
#include <array>
using namespace std;
int cnt(int x){return __builtin_popcount((unsigned)x);}
int first(int x){return __builtin_ctz((unsigned)x);}
int main(){
 string s; long long num[10]={};
 while(cin>>s){
 int n=s[0]-63, N=1<<n, a[9]={}, i,j,k=0;
 for(j=1;j<n;++j)for(i=0;i<j;++i,++k)
 if((s[1+k/6]-63)>>(5-k%6)&1){a[i]|=1<<j;a[j]|=1<<i;}
 int L=0,H=0,M=0,T=0,S=0,minDeg=n;
 for(i=0;i<n;i++)minDeg=min(minDeg,cnt(a[i]));
 for(i=0;i<n;i++){
  int d=cnt(a[i]);if(d==1)L|=1<<i,S|=a[i];
  if(d>=3)H|=1<<i;if(d*2>n)M|=1<<i;if(d==2)T|=1<<i;
 }
 int A=0,low=(N-1)^H,mid=(N-1)^M,pA=0,pT=0,pLow=0,meH=0,meMid=0;
 for(i=0;i<n;i++)if(cnt(a[i])==minDeg)A|=1<<i;
 for(i=0;i<n;i++){
 pA+=cnt(a[i]&A)==1;pT+=cnt(a[i]&T)==1;pLow+=cnt(a[i]&low)==1;
 if(H&(1<<i))meH+=cnt(a[i]&H);
 if(mid&(1<<i))meMid+=cnt(a[i]&mid);
 }
 int best=0;
 for(int x=1;x<N;x++){
  if(cnt(x)<=best)continue;
  bool ok=true;for(int q=x;q;q&=q-1)if(cnt(a[first(q)]&x)>1){ok=false;break;}
  if(ok)best=cnt(x);
 }
 // Held–Karp endpoint bitsets for arbitrary (not necessarily induced) paths.
 int ends[512]={},pc[512]={};
 for(int x=1;x<N;x++){
  if((x&(x-1))==0)ends[x]=x;
  else for(int q=x;q;q&=q-1){int i=first(q);if(a[i]&ends[x^(1<<i)])ends[x]|=1<<i;}
  if(ends[x])pc[x]=1;
  else{
   pc[x]=n;const int bit=x&-x;
   for(int sub=x;sub;sub=(sub-1)&x)if((sub&bit)&&ends[sub])pc[x]=min(pc[x],1+pc[x^sub]);
  }
 }
 if(best>pA+n-cnt(S)||best>cnt(M)+meMid/2+pc[N-1]||
    best>cnt(low)+meH/4||best>pT+n-cnt(S)+pLow){cerr<<"violation "<<s<<endl;return 1;}
 ++num[n];
 }
 for(int n=4;n<=9;n++)cout<<n<<' '<<num[n]<<endl;
}
```

</details>

AI-assisted work shared for review. No priority claim is made.
