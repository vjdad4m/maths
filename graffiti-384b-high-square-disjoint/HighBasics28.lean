import HighTable28

namespace Graffiti384b.HighSquare28
open SimpleGraph Finset Thin28 JointRank EarFrame33
open private Repair.nbr_mono Repair.full_nbr Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem supported_zero {W P : Finset V} {v : V} (b : ℕ) (support : 2≤nbr H v P) :
    hit H W P b v=0 := by
  unfold hit
  rw [card_eq_zero,filter_eq_empty_iff]
  intro k _ bad
  have low : nbr H v (P∪k)<2 := (mem_filter.mp bad).2
  exact (Nat.not_lt_of_ge (support.trans (Repair.nbr_mono H v
    (show P⊆P∪k from subset_union_left)))) low

def bill (m b a c : ℕ) := if c=0 then FiniteRange.badCount m b a
  else if c=1 then (m-1-a).choose b else 0

theorem bill_bound {W P : Finset V} (dis : Disjoint P W) {v : V} (vm : v∈W) (b : ℕ) :
    hit H W P b v≤bill W.card b (nbr H v W) (nbr H v P) := by
  classical
  by_cases none : nbr H v P=0
  · simpa [bill,none] using plain H (P:=P) (b:=b) vm
  by_cases one : nbr H v P=1
  · obtain ⟨z,zm⟩ := card_pos.mp (show 0<(P.filter (H.Adj v)).card from Nat.pos_of_ne_zero none)
    obtain ⟨zp,vz⟩ := mem_filter.mp zm
    simpa [bill,one,vm] using credited H (b:=b) zp (show z∉W from disjoint_left.mp dis zp) vz
  rw [supported_zero H b (by omega : 2≤nbr H v P)]
  exact Nat.zero_le _

theorem local_cap (free : H.CliqueFree 5) (v : V) :
    trianglesAt H v≤RankTable.cap (H.degree v) 3 ∨ 10≤H.degree v := by
  by_cases big : 10≤H.degree v
  · exact Or.inr big
  have tab := RankTable.cap_table ⟨H.degree v,by omega⟩ ⟨3,by decide⟩ (by decide)
  exact Or.inl ((RankTuran.local_turan H 3 (by decide) free v).trans_eq tab)

omit [Fintype V] in
theorem pool_degree {W : Finset V} {v : V} (vm : v∈W) : nbr H v W<W.card := by
  have sub : W.filter (H.Adj v)⊆W.erase v := by
    intro z zm; exact mem_erase.mpr ⟨(mem_filter.mp zm).2.ne.symm,(mem_filter.mp zm).1⟩
  have lim := card_le_card sub
  rw [card_erase_of_mem vm] at lim
  have nz := card_pos.mpr ⟨v,vm⟩
  change nbr H v W≤_ at lim
  omega

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.bill_bound
#print axioms Graffiti384b.HighSquare28.local_cap
