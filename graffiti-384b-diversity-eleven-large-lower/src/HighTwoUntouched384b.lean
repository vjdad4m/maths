import HighEarRetained384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Four baseline omissions can be supplemented by two high vertices
untouched by those omissions. The high vertices may be adjacent. -/
theorem exact_of_four_two_untouched (t : (types G).card=11)
    {O : Finset V} (four : 4≤O.card) (good : TwoDominates G Oᶜ)
    {a b : V} (ao : a∉O) (bo : b∉O) (ab : a≠b)
    (da : 3≤G.degree a) (db : 3≤G.degree b)
    (free : ∀ z∈O, ¬G.Adj z a ∧ ¬G.Adj z b) : gamma G≤bound G := by
  classical
  let T := insert a (insert b O)
  have mt (z : V) : z∈T ↔ z=a ∨ z=b ∨ z∈O := by simp [T]
  have six : 6≤T.card := by
    have ha : a∉insert b O := by simp [ab,ao]
    dsimp [T]
    rw [card_insert_of_not_mem ha,card_insert_of_not_mem bo]
    omega
  have help {u v : V} (d : 3≤G.degree u) (no : ∀ z∈O, ¬G.Adj u z)
      (sh : ∀ w, w∈T ↔ w=u ∨ w=v ∨ w∈O) : 2≤nbr G u Tᶜ := by
    have p : G.neighborFinset u ⊆ insert v (Tᶜ.filter (G.Adj u)) := by
      intro w wm
      have uw := (G.mem_neighborFinset ..).mp wm
      by_cases eq : w=v
      · exact mem_insert.mpr (Or.inl eq)
      refine mem_insert.mpr (Or.inr (mem_filter.mpr ⟨?_,uw⟩))
      rw [mem_compl,sh]
      rintro (rfl|h|h)
      · exact uw.ne rfl
      · exact eq h
      · exact no _ h uw
    have p1 := card_le_card p
    have p2 := card_insert_le v (Tᶜ.filter (G.Adj u))
    rw [card_neighborFinset_eq_degree] at p1
    unfold nbr
    omega
  have dom : TwoDominates G Tᶜ := by
    intro u h
    have mem : u∈T := by simpa using h
    rcases (mt u).mp mem with rfl|rfl|uo
    · exact help da (fun z zo az => (free z zo).1 az.symm) mt
    · exact help db (fun z zo bz => (free z zo).2 bz.symm)
        (fun w => by rw [mt]; tauto)
    · have sub : Oᶜ.filter (G.Adj u)⊆Tᶜ.filter (G.Adj u) := by
        intro w wm
        obtain ⟨wo,uw⟩ := mem_filter.mp wm
        apply mem_filter.mpr
        refine ⟨?_,uw⟩
        rw [mem_compl,mt]
        rintro (rfl|rfl|h)
        · exact (free u uo).1 uw
        · exact (free u uo).2 uw
        · exact (mem_compl.mp wo) h
      exact (good u (by simpa using uo)).trans (card_le_card sub)
  have gm : gamma G≤(Tᶜ).card :=
    Nat.sInf_le (s := {k : ℕ | ∃ d, TwoDominates G d ∧ d.card=k}) ⟨Tᶜ,dom,rfl⟩
  rw [card_compl] at gm
  unfold bound
  rw [t]
  omega

#print axioms exact_of_four_two_untouched
/-- Four independent nonleaf lows touching at most seven of nine high
vertices always give the extra two omissions. -/
theorem exact_of_four_low_footprint_seven (t : (types G).card=11)
    (nine : (high G).card=9) {O P : Finset V} (four : 4≤O.card)
    (low : Disjoint O (high G))
    (deg : ∀ x∈O,2≤G.degree x)
    (ind : ∀ x∈O,∀ y∈O,¬G.Adj x y)
    (touch : ∀ z∈high G,(∃ x∈O,G.Adj x z)→z∈P)
    (seven : P.card≤7) : gamma G≤bound G := by
  classical
  have c := card_sdiff_add_card_eq_card (show high G∩P ⊆ high G from inter_subset_left)
  have cap := card_le_card (show high G∩P ⊆ P from inter_subset_right)
  have enough : 1<((high G) \ (high G∩P)).card := by omega
  obtain ⟨a,am,b,bm,ab⟩ := Finset.one_lt_card.mp enough
  have aH := (mem_sdiff.mp am).1
  have bH := (mem_sdiff.mp bm).1
  have aP : a∉P := fun h => (mem_sdiff.mp am).2 (mem_inter.mpr ⟨aH,h⟩)
  have bP : b∉P := fun h => (mem_sdiff.mp bm).2 (mem_inter.mpr ⟨bH,h⟩)
  have dom : TwoDominates G Oᶜ := by
    intro x xo
    have xm : x∈O := by simpa using xo
    have eq : Oᶜ.filter (G.Adj x)=G.neighborFinset x := by
      ext y
      simp only [mem_filter,mem_neighborFinset]
      exact ⟨And.right,fun xy=>⟨mem_compl.mpr (fun ym=>ind x xm y ym xy),xy⟩⟩
    rw [nbr,eq,card_neighborFinset_eq_degree]
    exact deg x xm
  apply exact_of_four_two_untouched G t four dom
    (fun h=>Finset.disjoint_left.mp low h aH)
    (fun h=>Finset.disjoint_left.mp low h bH) ab (mem_filter.mp aH).2 (mem_filter.mp bH).2
  intro z zm
  exact ⟨fun za=>aP (touch a aH ⟨z,zm,za⟩),fun zb=>bP (touch b bH ⟨z,zm,zb⟩)⟩

#print axioms exact_of_four_low_footprint_seven
end Graffiti384b.DiversityEleven
