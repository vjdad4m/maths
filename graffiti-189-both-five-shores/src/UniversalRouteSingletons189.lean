import UniversalRouteBlocks189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
open private mem_blockCover from UniversalRouteBlocks189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

private noncomputable def singletonBlocks (R : Finset V) : List (Finset V) :=
  R.toList.map (fun z=>{z})

private theorem cover_singleton_blocks (R : Finset V) :
    blockCover (singletonBlocks R)=R := by
  ext z
  rw [mem_blockCover]
  constructor
  · rintro ⟨B,bm,zb⟩
    obtain ⟨w,wm,rfl⟩ := List.mem_map.mp bm
    have e := mem_singleton.mp zb
    exact e.symm ▸ (mem_toList.mp wm)
  intro zr
  exact ⟨{z},List.mem_map.mpr ⟨z,mem_toList.mpr zr,rfl⟩,mem_singleton_self _⟩

private theorem pair_singleton_blocks (R : Finset V) :
    (singletonBlocks R).Pairwise Disjoint := by
  unfold singletonBlocks
  rw [List.pairwise_map]
  exact (nodup_toList R).imp (fun h=>by simpa using h.symm)

private theorem routes_singleton_blocks {R B : Finset V} (h : B∈singletonBlocks R) :
    ∃ u∈B,∃ v∈B,RouteOn G B u v := by
  classical
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
  exact ⟨z,mem_singleton_self _,z,mem_singleton_self _,RouteOn.singleton⟩

/-- The residual vertices can all be taken as singletons. -/
theorem universal_route_from_singletons
    (K R : Finset V) {x : V} (xk : x∈K)
    (apart : Disjoint K R)
    (join : ∀ u∈K,∀ w∈K∪R,u≠w → G.Adj u w)
    (enough : R.card≤K.card) :
    ∃ y,RouteOn G (K∪R) x y ∧ (R.card<K.card → y∈K) := by
  let L := singletonBlocks R
  have eq : blockCover L=R := cover_singleton_blocks R
  have len : L.length=R.card := by simp [L,singletonBlocks]
  obtain ⟨y,route,stop⟩ := universal_route_from_blocks L K xk (pair_singleton_blocks R)
    (by rwa [eq]) (fun B m=>routes_singleton_blocks m) (by rwa [eq]) (by rwa [len])
  exact ⟨y,eq ▸ route,fun h=>stop (by rwa [len])⟩

/-- One spanning block saves as many separators as its size minus one. -/
theorem universal_route_with_one_block
    (K R P : Finset V) {x u v : V} (xk : x∈K) (uP : u∈P) (vP : v∈P)
    (apart : Disjoint K R) (pr : P⊆R)
    (route : RouteOn G P u v)
    (join : ∀ z∈K,∀ w∈K∪R,z≠w → G.Adj z w)
    (enough : (R\P).card+1≤K.card) :
    ∃ y,RouteOn G (K∪R) x y ∧ ((R\P).card+1<K.card → y∈K) := by
  let M := singletonBlocks (R\P)
  let L := P::M
  have cov : blockCover L=R := by
    change P∪blockCover M=R
    rw [cover_singleton_blocks,union_sdiff_of_subset pr]
  have len : L.length=(R\P).card+1 := by simp [L,M,singletonBlocks]
  have d : Disjoint P (R\P) := by
    apply disjoint_left.mpr
    intro z zp zr
    exact (mem_sdiff.mp zr).2 zp
  have pair : L.Pairwise Disjoint := by
    apply List.pairwise_cons.mpr
    refine ⟨?_,pair_singleton_blocks (R\P)⟩
    intro B bm
    obtain ⟨w,wm,rfl⟩ := List.mem_map.mp bm
    exact d.mono_right (singleton_subset_iff.mpr (mem_toList.mp wm))
  have all (B : Finset V) (bm : B∈L) : ∃ p∈B,∃ q∈B,RouteOn G B p q := by
    rcases List.mem_cons.mp bm with rfl|rest
    · exact ⟨u,uP,v,vP,route⟩
    exact routes_singleton_blocks rest
  obtain ⟨y,p,stop⟩ := universal_route_from_blocks L K xk pair
    (by rwa [cov]) all (by rwa [cov]) (by rwa [len])
  exact ⟨y,cov ▸ p,fun h=>stop (by rwa [len])⟩

#print axioms universal_route_from_singletons
#print axioms universal_route_with_one_block
end Graffiti189LongestPath.CrossSaturation
