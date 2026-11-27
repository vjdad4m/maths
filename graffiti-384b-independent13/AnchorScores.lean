import IndependentFrontier
namespace Graffiti384b.Reserved16
open Finset SimpleGraph
open private Repair.linkEdges Repair.edge_info from Repair384b
open private Joint17.transpose from JointEarRank
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Apart from the possible edge between the ear and the other anchor,
an adjacent pair in the anchor neighborhood has both vertices in X. -/
theorem anchor_score {e w b : V} (ear : G.neighborFinset e={w,b})
    (priv : G.neighborFinset w∩G.neighborFinset b={e}) (X : Finset V)
    (xd : X=high G\{w,b}) (other : ∀ v,G.degree v=2 → v≠e → G.neighborFinset v⊆X) :
    trianglesAt G b≤1+(nbr G b X).choose 2 := by
  classical
  have mate {i j : V} (bi : G.Adj b i) (bj : G.Adj b j) (ij : G.Adj i j) (ins : i∈({w,e} : Finset V)) :
      ({i,j} : Finset V)={w,e} := by
    rcases mem_insert.mp ins with rfl|m
    · have jm : j∈G.neighborFinset i∩G.neighborFinset b := mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr ij,(G.mem_neighborFinset _ _).mpr bj⟩
      rw [priv,mem_singleton] at jm
      rw [jm]
    · obtain rfl := mem_singleton.mp m
      have jm := (G.mem_neighborFinset _ _).mpr ij
      rw [ear,mem_insert,mem_singleton] at jm
      rw [jm.resolve_right bj.ne.symm,pair_comm]
  have cover : Repair.linkEdges G b⊆insert {w,e} ((X.filter (G.Adj b)).powersetCard 2) := by
    intro a am
    obtain ⟨sub,sz,cl⟩ := Repair.edge_info G am
    obtain ⟨i,j,ne,eq⟩ := card_eq_two.mp sz
    have im : i∈a := eq ▸ mem_insert_self .. 
    have jm : j∈a := eq ▸ mem_insert_of_mem (mem_singleton_self _)
    have bi := (G.mem_neighborFinset _ _).mp (sub im)
    have bj := (G.mem_neighborFinset _ _).mp (sub jm)
    have ij := cl _ im _ jm ne
    by_cases hi : i∈({w,e} : Finset V)
    · exact mem_insert.mpr (Or.inl (eq.trans (mate bi bj ij hi)))
    by_cases hj : j∈({w,e} : Finset V)
    · exact mem_insert.mpr (Or.inl (eq.trans ((pair_comm ..).trans (mate bj bi ij.symm hj))))
    have inPool {u v : V} (bu : G.Adj b u) (bv : G.Adj b v) (uv : G.Adj u v) (off : u∉({w,e}:Finset V)) : u∈X := by
      have inc : ({b,v}:Finset V)⊆G.neighborFinset u := insert_subset ((G.mem_neighborFinset ..).mpr bu.symm)
        (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr uv))
      have dg := card_le_card inc
      rw [card_pair bv.ne,card_neighborFinset_eq_degree] at dg
      have ne : u≠e := fun eq => off (eq ▸ mem_insert_of_mem (mem_singleton_self _))
      have high' : 3≤G.degree u := by
        by_contra! small
        have bx := other u (by omega) ne ((G.mem_neighborFinset ..).mpr bu.symm)
        rw [xd] at bx
        exact (mem_sdiff.mp bx).2 (mem_insert_of_mem (mem_singleton_self _))
      rw [xd]; apply mem_sdiff.mpr
      exact ⟨mem_filter.mpr ⟨mem_univ _,high'⟩,by simp [bu.ne.symm,show u≠w from fun eq => off (eq ▸ mem_insert_self ..)]⟩
    have ix := inPool bi bj ij hi
    have jx := inPool bj bi ij.symm hj
    refine mem_insert_of_mem (mem_powersetCard.mpr ⟨?_,sz⟩)
    rw [eq]; exact insert_subset (mem_filter.mpr ⟨ix,bi⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨jx,bj⟩))
  have cap := (card_le_card cover).trans (card_insert_le ..)
  rw [card_powersetCard] at cap
  exact cap.trans_eq (Nat.add_comm ..)

/-- With at most twelve exterior high contacts, at least one anchor
has score at most eleven or both scores are at most sixteen. -/
theorem score_alternatives {e a b : V} (ear : G.neighborFinset e={a,b})
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (X : Finset V)
    (xd : X=high G\{a,b}) (other : ∀ v,G.degree v=2 → v≠e → G.neighborFinset v⊆X)
    (cap : nbr G a X+nbr G b X≤12) :
    trianglesAt G a≤11 ∨ trianglesAt G b≤11 ∨ (trianglesAt G a≤16 ∧ trianglesAt G b≤16) := by
  have sb := anchor_score G ear thin X xd other
  have sa := anchor_score G (ear.trans (pair_comm ..)) ((inter_comm ..).trans thin) X (by rw [xd,pair_comm a b]) other
  have lim {v : V} (small : nbr G v X≤5) (bound' : trianglesAt G v≤1+(nbr G v X).choose 2) : trianglesAt G v≤11 := by
    have up := Nat.choose_le_choose 2 small
    rw [show (5:ℕ).choose 2=10 by decide] at up; omega
  by_cases a' : nbr G a X≤5
  · exact Or.inl (lim a' sa)
  by_cases b' : nbr G b X≤5
  · exact Or.inr (Or.inl (lim b' sb))
  have aa : nbr G a X=6 := by omega
  have bb : nbr G b X=6 := by omega
  rw [aa,show (6:ℕ).choose 2=15 by decide] at sa
  rw [bb,show (6:ℕ).choose 2=15 by decide] at sb
  exact Or.inr (Or.inr ⟨sa,sb⟩)

end Graffiti384b.Reserved16
#print axioms Graffiti384b.Reserved16.anchor_score
#print axioms Graffiti384b.Reserved16.score_alternatives
