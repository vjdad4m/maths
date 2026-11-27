import FrontierDegrees31
import FrontierRoots31

namespace Graffiti384b.Frontier31
open Finset SimpleGraph
open private Frontier31.local_clique from Frontier31Finish
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def DenseCenter (v : V) : Prop :=
  5≤G.degree v ∧ G.degree v≤8 ∧ RankTable.cap (G.degree v) 3<trianglesAt G v ∧
    ∃ C : Finset V,G.IsNClique 5 C ∧ v∈C

/-- At the middle nonleaf quota even a center of degree four is insufficient. -/
theorem one_center (t : (types G).card=31) (q : 31≤(nonleaves G).card) (bad : bound G<gamma G) :
    ∃ v,DenseCenter G v := by
  obtain ⟨v,l,h,_,s⟩ := avoiding G (skip:=0) (by decide) t q bad
  exact ⟨v,l,h,s,Frontier31.local_clique G (by omega) s⟩

/-- At the largest surviving quota two different degrees in 5,6,7,8
must occur as dense centers on five-cliques. -/
theorem two_centers (t : (types G).card=31) (q : 32≤(nonleaves G).card) (bad : bound G<gamma G) :
    ∃ u v,DenseCenter G u ∧ DenseCenter G v ∧ G.degree u≠G.degree v := by
  obtain ⟨u,cu⟩ := one_center G t (by omega) bad
  have lo := cu.1
  have hi := cu.2.1
  have sk : G.degree u∈({0,5,6,7,8}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
  have need : DegreeRows.required (G.degree u)=32 := by simp [DegreeRows.required,show G.degree u≠0 by omega]
  obtain ⟨v,l,h,ne,s⟩ := avoiding G sk t (need ▸ q) bad
  exact ⟨u,v,cu,⟨l,h,s,Frontier31.local_clique G (by omega) s⟩,ne.symm⟩

/-- Exact nonleaf cases for every connected failure of diversity 31. -/
theorem alternatives (hc : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=31) (bad : bound G<gamma G) :
    ((nonleaves G).card=30 ∧ ∃ S : Finset V,S.card=31 ∧ (G.induce (S:Set V)).Connected ∧
      types (G.induce (S:Set V))=types G ∧ bound (G.induce (S:Set V))<gamma (G.induce (S:Set V))) ∨
    ((nonleaves G).card=31 ∧ ∃ v,DenseCenter G v) ∨
    ((nonleaves G).card=32 ∧ ∃ u v,DenseCenter G u ∧ DenseCenter G v ∧ G.degree u≠G.degree v) := by
  have l := enough G t
  have h := Below33.nonleaf_cap G (by omega) hc hn bad
  by_cases q : (nonleaves G).card=30
  · obtain ⟨S,_,cap,_,con,same,fail⟩ := Prune.prune_failure G hc hn bad
    have size : (types (G.induce (S:Set V))).card≤S.card := by
      simpa [types] using (card_image_le (s:=(univ:Finset S)) (f:=trianglesAt (G.induce (S:Set V))))
    rw [same,t] at size
    exact Or.inl ⟨q,S,by omega,con,same,fail⟩
  by_cases m : (nonleaves G).card=31
  · exact Or.inr (Or.inl ⟨m,one_center G t m.ge bad⟩)
  exact Or.inr (Or.inr ⟨by omega,two_centers G t (by omega) bad⟩)

/-- A single degree among the candidate centers suffices to settle
diversity 31 when the graph has at least 32 nonleaves. -/
theorem exact_of_single_center_degree (t : (types G).card=31) (q : 32≤(nonleaves G).card)
    (one : ∀ u v,DenseCenter G u → DenseCenter G v → G.degree u=G.degree v) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨u,v,uc,vc,ne⟩ := two_centers G t q bad
  exact ne (one u v uc vc)

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.one_center
#print axioms Graffiti384b.Frontier31.two_centers
#print axioms Graffiti384b.Frontier31.alternatives
#print axioms Graffiti384b.Frontier31.exact_of_single_center_degree
