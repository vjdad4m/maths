import BagTransfer180
import DomRoot180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
theorem Bags.hubEdge (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    {c : B} (hub : Universal G c) (r : V) : ∃ y, DomEdge H r y := by
  classical
  by_cases root : f r=c
  · obtain ⟨j,cj⟩ := exists_adj G gc hn c
    obtain ⟨y,fy⟩ := h.onto j
    have edge : H.Adj r y := h.edgeUp (by rwa [root,fy])
    refine ⟨y,edge,fun x _ _ => ?_⟩
    by_cases eq : f x=c
    · exact Or.inr (h.edgeUp (by rwa [eq,fy]))
    · exact Or.inl (h.edgeUp (by rw [root]; exact hub _ eq))
  · obtain ⟨y,fy⟩ := h.onto c
    have edge : H.Adj r y := h.edgeUp (by rw [fy]; exact hub _ root)
    refine ⟨y,edge,fun x _ _ => ?_⟩
    by_cases eq : f x=c
    · exact Or.inl (h.edgeUp (by rw [eq]; exact (hub _ root).symm))
    · exact Or.inr (h.edgeUp (by rw [fy]; exact hub _ eq))

omit [DecidableEq B] in
theorem three_of_nohub (G : SimpleGraph B) (gc : G.Connected) (hn : 1<Fintype.card B)
    (nh : ∀ i,¬Universal G i) : 2<Fintype.card B := by
  classical
  obtain ⟨r⟩ := gc.nonempty
  obtain ⟨y,ry⟩ := exists_adj G gc hn r
  obtain ⟨z,zr,no⟩ : ∃ z,z≠r ∧ ¬G.Adj z r := by simpa [Universal] using nh r
  have zy : z≠y := fun e => no (e ▸ ry.symm)
  have n := card_le_univ ({z,r,y}:Finset B)
  rw [card_insert_of_not_mem (by simp [zr,zy]),card_pair ry.ne] at n; omega

/-- The base's one rooted inequality suffices for its entire substitution
at that same root and parity. A base with a universal vertex needs no
inductive hypothesis. -/
theorem Bags.rooted (h : Bags H G f) (cover : CoversBags H G f) (gc : G.Connected)
    (hn : 1<Fintype.card B) (r : V) (p : Bool) (base : localBound G (f r) (parity G (f r) p)) :
    localBound H r (parity H r p) := by
  classical
  by_cases top : ∃ c,Universal G c
  · obtain ⟨c,uc⟩ := top
    obtain ⟨_,e⟩ := h.hubEdge gc hn uc r
    have n := Fintype.card_le_of_surjective f h.onto
    exact dom_edge_rooted H (h.connected gc hn) (by omega) e p
  · have nh : ∀ i,¬Universal G i := by simpa using top
    exact h.localLift cover gc (three_of_nohub G gc hn nh) nh r p base

/-- A failed marking descends to a strictly smaller base for every proper
substitution covered by the bipartite-witness condition. -/
theorem Bags.strictDescent (h : Bags H G f) (cover : CoversBags H G f) (gc : G.Connected)
    (hn : 1<Fintype.card B) (proper : ¬Function.Injective f) (r : V) (p : Bool)
    (bad : ¬localBound H r (parity H r p)) :
    Fintype.card B<Fintype.card V ∧ ¬localBound G (f r) (parity G (f r) p) :=
  ⟨Fintype.card_lt_of_surjective_not_injective f h.onto proper,fun old => bad (h.rooted cover gc hn r p old)⟩

omit [Fintype V] [DecidableEq V] in
theorem cover_bipartite (H : SimpleGraph V) (G : SimpleGraph B) (f : V→B)
    (bi : TwoColor G univ) : CoversBags H G f := by
  classical
  intro I _
  obtain ⟨Z,_,sz⟩ := optB G
  have cap := card_le_univ Z
  refine ⟨univ,bi,le_antisymm (size_bip G bi) ?_,fun _ _ _ => mem_univ _⟩
  simpa only [card_univ,sz] using cap

omit [Fintype V] [DecidableEq V] in
theorem cover_cliques (H : SimpleGraph V) (G : SimpleGraph B) (f : V→B)
    (cl : ∀ x y,f x=f y → x≠y → H.Adj x y) : CoversBags H G f := by
  intro I _
  obtain ⟨Z,col,sz⟩ := optB G
  refine ⟨Z,col,sz,?_⟩
  rintro i _ ⟨x,y,xi,yi,ne,no⟩
  exact (no (cl x y (xi.trans yi.symm) ne)).elim

/-- Every substitution of nonempty arbitrary graphs into a connected
nontrivial bipartite base satisfies every rooted inequality, with no
bound on diameter or on the number of vertices needed for bipartization. -/
theorem Bags.bipartiteRooted (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (bi : TwoColor G univ) (r : V) (p : Bool) : localBound H r (parity H r p) := by
  apply h.rooted (cover_bipartite H G f bi) gc hn r p
  intro A ai
  have low := weighted_bipartite G gc hn bi (f r) p.toNat A ai
  change A.card+(parity G (f r) p).card+1≤bipartiteNum G+weightedLeaves G (eligible A (parity G (f r) p) (f r)) at low
  omega

#print axioms Bags.hubEdge
#print axioms Bags.rooted
#print axioms Bags.strictDescent
#print axioms cover_bipartite
#print axioms cover_cliques
#print axioms Bags.bipartiteRooted
end Minimal180.Substitution
