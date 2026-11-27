import RemoteT2NontrivialBridge
import RemoteT2ForcedChain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2LeafBridgeFactor
open SquareCap (SmallTrivial FactorOn)
open RemoteT2PairCounts (OutsideTwo innerCut)
open RemoteT2PairStructure (surviving)
open RemoteT2Scope (cyclic_four_pair_no_common)
open RemoteT2NontrivialBridge (leaf_and_balanced_cut_small_shore)
open RemoteT2ForcedChain (factor_iff_strip_leaf_chain)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
def omitEdge (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬(a=u∧b=v ∨ a=v∧b=u)
  symm := by
    rintro a b ⟨e,h⟩
    refine ⟨e.symm,?_⟩
    rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact h (Or.inr ⟨rfl,rfl⟩)
    · exact h (Or.inl ⟨rfl,rfl⟩)
  loopless := fun a h=> G.loopless a h.1

def rest (x y : V) : Finset V := (univ.erase x).erase y

@[simp] theorem mem_rest {x y a : V} : a∈rest x y↔a≠x∧a≠y := by simp [rest,and_comm]

private theorem pool_has {x y w z : V} (zx : z≠x) (zy : z≠y) (e : G.Adj w z) :
    z∈surviving G x y w :=
  mem_erase.mpr ⟨zy,mem_erase.mpr ⟨zx,(mem_neighborFinset _ _ _).mpr e⟩⟩

private theorem pool_has_two {x y w : V} (d : G.degree w=3)
    (h : (G.Adj w x ∧ ¬G.Adj w y) ∨ (G.Adj w y ∧ ¬G.Adj w x)) :
    (surviving G x y w).card=2 := by
  unfold surviving
  rcases h with ⟨hx,hy⟩|⟨hy,hx⟩
  · have ny : y∉(G.neighborFinset w).erase x :=
      fun m=>hy ((mem_neighborFinset _ _ _).mp (mem_erase.mp m).2)
    rw [erase_eq_of_not_mem ny,card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hx),
      card_neighborFinset_eq_degree,d]
  · have nx : x∉G.neighborFinset w := fun m=>hx ((mem_neighborFinset _ _ _).mp m)
    rw [erase_eq_of_not_mem nx,card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hy),
      card_neighborFinset_eq_degree,d]

/-- If a nontrivial bridge and a leaf bridge coexist in the remote-deleted
graph, the left shore has precisely the leaf u and its neighbor w; every
factor must use their unique three-vertex chain across the second bridge.
The right side of the iff is only a reduction, not a claim that it factors. -/
theorem factor_iff_strip_square_arm (small : SmallTrivial G)
    (big : 5≤Fintype.card V) (cub : ∀ w : V, G.degree w=3)
    {x y u v : V} (xy : G.Adj x y) (uv : G.Adj u v)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (uyEdge : G.Adj u y) {c : V→Bool} (cu : c u=true) (cv : c v=false)
    (cp : OutsideTwo c x y true) (cn : OutsideTwo c x y false)
    (C : (innerCut G c x y).card=2)
    (leafWidth : (innerCut G (fun z=>decide (z=u)) x y).card=2) :
    ∃ w q : V, w∈rest x y ∧ q∈rest x y ∧ G.Adj x w ∧ G.Adj u w ∧
      G.Adj w q ∧ c q=false ∧
      (FactorOn (omitEdge G u v) (rest x y) ↔
        FactorOn (omitEdge G u v) ((rest x y) \ ({u,w,q}:Finset V))) := by
  classical
  obtain ⟨w,wx,wy,wu,xw,uw,precise⟩ :=
    leaf_and_balanced_cut_small_shore G small big cub xy uv ux uy vx vy uyEdge cu cv cp cn C leafWidth
  have wyEdge : ¬G.Adj w y := fun e=>cyclic_four_pair_no_common small big cub xy w ⟨xw,e.symm⟩
  have uxEdge : ¬G.Adj u x := fun e=>cyclic_four_pair_no_common small big cub xy u ⟨e.symm,uyEdge.symm⟩
  have wv : w≠v := by
    intro e
    subst v
    have wc := (precise w wx wy).mpr (Or.inr rfl)
    rw [cv] at wc
    contradiction
  have sizeU := pool_has_two G (cub u) (Or.inr ⟨uyEdge,uxEdge⟩)
  have sizeW := pool_has_two G (cub w) (Or.inl ⟨xw.symm,wyEdge⟩)
  have U : surviving G x y u={w,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact pool_has G wx wy uw
      · exact pool_has G vx vy uv
    · simp [sizeU,wv]
  have WU : u∈surviving G x y w := pool_has G ux uy uw.symm
  have er : ((surviving G x y w).erase u).card=1 := by rw [card_erase_of_mem WU,sizeW]
  obtain ⟨q,Hq⟩ := card_eq_one.mp er
  have qm : q∈(surviving G x y w).erase u := by rw [Hq]; simp
  obtain ⟨qu,Rq⟩ := mem_erase.mp qm
  obtain ⟨qy,Sq⟩ := mem_erase.mp Rq
  obtain ⟨qx,Nq⟩ := mem_erase.mp Sq
  have wq := (mem_neighborFinset _ _ _).mp Nq
  have qf : c q=false := by
    cases k : c q
    · rfl
    · rcases (precise q qx qy).mp k with e|e
      · exact False.elim (qu e)
      · exact False.elim (wq.ne e.symm)
  refine ⟨w,q,mem_rest.mpr ⟨wx,wy⟩,mem_rest.mpr ⟨qx,qy⟩,xw,uw,wq,qf,?_⟩
  apply factor_iff_strip_leaf_chain (mem_rest.mpr ⟨ux,uy⟩)
    (mem_rest.mpr ⟨wx,wy⟩) (mem_rest.mpr ⟨qx,qy⟩) qu.symm
  · exact ⟨uw,fun h=>h.elim (fun p=>wv p.2) (fun p=>uv.ne p.1)⟩
  · exact ⟨wq,fun h=>h.elim (fun p=>wu p.1) (fun p=>wv p.1)⟩
  · intro z zr h
    obtain ⟨zx,zy⟩ := mem_rest.mp zr
    have m := pool_has G zx zy h.1
    rw [U] at m
    rcases mem_insert.mp m with e|e
    · exact e
    · have ev := mem_singleton.mp e
      subst z
      exact False.elim (h.2 (Or.inl ⟨rfl,rfl⟩))
  · intro z zr h
    obtain ⟨zx,zy⟩ := mem_rest.mp zr
    by_cases zu : z=u
    · exact Or.inl zu
    · apply Or.inr
      have m : z∈(surviving G x y w).erase u := mem_erase.mpr ⟨zu,pool_has G zx zy h.1⟩
      rwa [Hq,mem_singleton] at m

#print axioms factor_iff_strip_square_arm
end KelmansCactus.AtomicBridge.RemoteT2LeafBridgeFactor
