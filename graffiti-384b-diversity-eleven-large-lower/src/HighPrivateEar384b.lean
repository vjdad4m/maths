import HighEarSwap384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A five-omission baseline and a marked edge whose two high endpoints each
touch only that ear among the omissions gives the exact diversity-eleven
bound. This covers either matching profile once its private ear is supplied. -/
theorem exact_of_five_with_private_ear (t : (types G).card=11)
    {O : Finset V} (five : 5≤O.card) (good : TwoDominates G Oᶜ)
    {e a b : V} (he : e∈O) (ha : a∉O) (hb : b∉O) (ab : a≠b)
    (ae : G.Adj a e) (be : G.Adj b e)
    (da : 3≤G.degree a) (db : 3≤G.degree b)
    (alone : ∀ z∈O, z≠e → ¬G.Adj z a ∧ ¬G.Adj z b) :
    gamma G≤bound G := by
  classical
  have extra {u v : V} (d : 3≤G.degree u)
      (no : ∀ z∈O, z≠e → ¬G.Adj u z) :
      ∃ x∉O, x≠u ∧ x≠v ∧ G.Adj u x := by
    by_contra! n
    have sub : G.neighborFinset u ⊆ ({e,v} : Finset V) := by
      intro x xm
      have ux := (G.mem_neighborFinset ..).mp xm
      by_cases h : x∈O
      · have eq : x=e := by by_contra ne; exact no x h ne ux
        exact mem_insert.mpr (Or.inl eq)
      · have eq : x=v := by
          by_contra ne
          exact n x h ux.ne.symm ne ux
        exact mem_insert.mpr (Or.inr (mem_singleton.mpr eq))
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree] at c
    have cap := card_insert_le e ({v} : Finset V)
    rw [card_singleton] at cap
    omega
  apply exact_of_ear_swap G t five good he ha hb ab ae be
  · exact extra da (fun z zm nz az => (alone z zm nz).1 az.symm)
  · obtain ⟨x,xo,xb,xa,bx⟩ := extra (v:=a) db (fun z zm nz bz =>
      (alone z zm nz).2 bz.symm)
    exact ⟨x,xo,xa,xb,bx⟩
  · exact alone

#print axioms exact_of_five_with_private_ear
end Graffiti384b.DiversityEleven
