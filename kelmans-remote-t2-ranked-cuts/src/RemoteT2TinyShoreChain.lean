import RemoteT2PairStructure
import RemoteT2CompletionTransfer
import RemoteT2ForcedChain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2TinyShoreChain
open SquareCap (SmallTrivial FactorOn boundary)
open RemoteT2PairStructure (surviving surviving_card_lb)
open RemoteT2PairCounts (innerCut)
open RemoteT2CompletionTransfer (eraseEdge marked)
open RemoteT2ForcedChain (factor_iff_strip_leaf_chain)
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def outside (x y : V) : Finset V := (univ.erase x).erase y

@[simp] theorem mem_outside {z x y : V} :
    z∈outside x y ↔ z≠x∧z≠y := by simp [outside,and_comm]

private theorem in_pool {x y a z : V} :
    z∈surviving G x y a ↔ z≠x∧z≠y∧G.Adj a z := by
  simp [surviving,mem_neighborFinset,and_comm,and_left_comm]

omit [DecidableRel G.Adj] in
private theorem in_inner {c : V→Bool} {x y a z : V} :
    (a,z)∈innerCut G c x y ↔
      (c a=true∧c z=false∧G.Adj a z)∧a≠x∧a≠y∧z≠x∧z≠y := by
  classical
  simp [innerCut,boundary]

omit [Fintype V] in
private theorem erase_lb {T : Finset V} (h : 2≤T.card) (w : V) :
    1≤(T.erase w).card := by
  by_cases m : w∈T
  · rw [card_erase_of_mem m]; omega
  · rw [erase_eq_of_not_mem m]; omega

/-- A surviving width-two cut whose true shore has two vertices is
a forced three-vertex chain after omitting either crossing edge.
This uses no remoteness restriction and no factor-existence
hypothesis. Both vertices are forced to meet one removed vertex
in the cubic host (the statement exposes the actual surviving
neighbor sets). -/
theorem tiny_width_two_chain
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ z,G.degree z=3)
    {x y u v w : V} (xy : G.Adj x y)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y) (wx : w≠x) (wy : w≠y)
    (uw : u≠w) (uv : G.Adj u v)
    (c : V→Bool) (cu : c u=true) (cv : c v=false) (cw : c w=true)
    (precise : ∀ z : V,z≠x → z≠y → (c z=true ↔ z=u∨z=w))
    (cut : (innerCut G c x y).card=2) :
    ∃ q : V,q≠x∧q≠y∧c q=false∧G.Adj u w∧G.Adj w q∧
      surviving G x y u={w,v}∧surviving G x y w={u,q}∧
      (FactorOn (eraseEdge G u v) (outside x y) ↔
        FactorOn (eraseEdge G u v) (outside x y \ ({u,w,q}:Finset V))) := by
  classical
  let P := (surviving G x y u).erase w
  let Q := (surviving G x y w).erase u
  let fu : V→V×V := fun z=>(u,z)
  let fw : V→V×V := fun z=>(w,z)
  have bv : v≠w := fun eq=>(by decide : false≠true) (cv.symm.trans (eq ▸ cw))
  have onlyU (z : V) (m : z∈P) : c z=false := by
    obtain ⟨zo,p⟩ := mem_erase.mp m
    obtain ⟨zx,zy,e⟩ := (in_pool G).mp p
    cases h : c z
    · rfl
    · exact False.elim (((precise z zx zy).mp h).elim (fun eq=>e.ne eq.symm) zo)
  have onlyW (z : V) (m : z∈Q) : c z=false := by
    obtain ⟨zo,p⟩ := mem_erase.mp m
    obtain ⟨zx,zy,e⟩ := (in_pool G).mp p
    cases h : c z
    · rfl
    · exact False.elim (((precise z zx zy).mp h).elim zo (fun eq=>e.ne eq.symm))
  have countIdentity : innerCut G c x y=(P.image fu)∪(Q.image fw) := by
    ext ⟨a,z⟩
    constructor
    · intro m
      obtain ⟨⟨ac,zc,ed⟩,ax,ay,zx,zy⟩ := (in_inner G).mp m
      rcases (precise a ax ay).mp ac with rfl|rfl
      · have zw : z≠w := fun eq=>(by decide : false≠true) (zc.symm.trans (eq ▸ cw))
        exact mem_union_left _ (mem_image.mpr ⟨z,mem_erase.mpr ⟨zw,(in_pool G).mpr ⟨zx,zy,ed⟩⟩,rfl⟩)
      · have zu : z≠u := fun eq=>(by decide : false≠true) (zc.symm.trans (eq ▸ cu))
        exact mem_union_right _ (mem_image.mpr ⟨z,mem_erase.mpr ⟨zu,(in_pool G).mpr ⟨zx,zy,ed⟩⟩,rfl⟩)
    · intro m
      rcases mem_union.mp m with hm|hm
      · obtain ⟨b,hb,h⟩ := mem_image.mp hm
        change (u,b)=(a,z) at h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        obtain ⟨zx,zy,ed⟩ := (in_pool G).mp (mem_erase.mp hb).2
        exact (in_inner G).mpr ⟨⟨cu,onlyU _ hb,ed⟩,ux,uy,zx,zy⟩
      · obtain ⟨b,hb,h⟩ := mem_image.mp hm
        change (w,b)=(a,z) at h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        obtain ⟨zx,zy,ed⟩ := (in_pool G).mp (mem_erase.mp hb).2
        exact (in_inner G).mpr ⟨⟨cw,onlyW _ hb,ed⟩,wx,wy,zx,zy⟩
  have disj : Disjoint (P.image fu) (Q.image fw) := by
    apply disjoint_left.mpr
    intro e p q
    obtain ⟨a,_,rfl⟩ := mem_image.mp p
    obtain ⟨b,_,eq⟩ := mem_image.mp q
    exact uw (congrArg Prod.fst eq.symm)
  have joined : P.card+Q.card=2 := by
    rwa [countIdentity,card_union_of_disjoint disj,
      card_image_of_injective _ (fun _ _ h=>congrArg Prod.snd h),
      card_image_of_injective _ (fun _ _ h=>congrArg Prod.snd h)] at cut
  have lb (z : V) : 2≤(surviving G x y z).card := by
    apply surviving_card_lb G (cub z)
    rintro ⟨a,b⟩
    exact RemoteT2Scope.cyclic_four_pair_no_common small big cub xy z ⟨a.symm,b.symm⟩
  have bp : 1≤P.card := erase_lb (lb u) w
  have bq : 1≤Q.card := erase_lb (lb w) u
  have cp : P.card=1 := by omega
  have cq : Q.card=1 := by omega
  have adj : G.Adj u w := by
    by_cases yes : G.Adj u w
    · exact yes
    · exfalso
      have absent : w∉surviving G x y u := fun m=>yes ((in_pool G).mp m).2.2
      have p0 := lb u
      change ((surviving G x y u).erase w).card=1 at cp
      rw [erase_eq_of_not_mem absent] at cp
      omega
  have mV : v∈P := mem_erase.mpr ⟨bv,(in_pool G).mpr ⟨vx,vy,uv⟩⟩
  obtain ⟨v',vp⟩ := card_eq_one.mp cp
  have vv : v=v' := by simpa [vp] using mV
  have pv : P={v} := by rwa [←vv] at vp
  obtain ⟨q,qp⟩ := card_eq_one.mp cq
  have qm : q∈Q := by rw [qp]; simp
  have qu : q≠u := (mem_erase.mp qm).1
  obtain ⟨qx,qy,wq⟩ := (in_pool G).mp (mem_erase.mp qm).2
  have qf := onlyW q qm
  have wIn : w∈surviving G x y u := (in_pool G).mpr ⟨wx,wy,adj⟩
  have uIn : u∈surviving G x y w := (in_pool G).mpr ⟨ux,uy,adj.symm⟩
  have pu : surviving G x y u={w,v} := by
    have e := insert_erase wIn
    change insert w P=surviving G x y u at e
    rw [pv] at e
    exact e.symm
  have pq : surviving G x y w={u,q} := by
    have e := insert_erase uIn
    change insert u Q=surviving G x y w at e
    rw [qp] at e
    exact e.symm
  refine ⟨q,qx,qy,qf,adj,wq,pu,pq,?_⟩
  apply factor_iff_strip_leaf_chain (mem_outside.mpr ⟨ux,uy⟩)
    (mem_outside.mpr ⟨wx,wy⟩) (mem_outside.mpr ⟨qx,qy⟩) qu.symm
  · exact ⟨adj,fun h=>h.elim (fun p=>bv p.2.symm) (fun p=>uv.ne p.1)⟩
  · exact ⟨wq,fun h=>h.elim (fun p=>uw p.1.symm) (fun p=>bv p.1.symm)⟩
  · intro z zm e
    obtain ⟨zx,zy⟩ := mem_outside.mp zm
    have p : z∈surviving G x y u := (in_pool G).mpr ⟨zx,zy,e.1⟩
    rw [pu,mem_insert,mem_singleton] at p
    rcases p with rfl|rfl
    · rfl
    · exact False.elim (e.2 (Or.inl ⟨rfl,rfl⟩))
  · intro z zm e
    obtain ⟨zx,zy⟩ := mem_outside.mp zm
    have p : z∈surviving G x y w := (in_pool G).mpr ⟨zx,zy,e.1⟩
    rwa [pq,mem_insert,mem_singleton] at p

#print axioms tiny_width_two_chain
end KelmansCactus.AtomicBridge.RemoteT2TinyShoreChain
