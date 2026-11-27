import P5CliqueFourPortPacking133

namespace Graffiti133FourPortPacking
open SimpleGraph Finset Graffiti133
open scoped Classical
set_option maxHeartbeats 1000000
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem two_ports_in_image (p : Fin 4 → V) (pi : Function.Injective p)
    {h a : Fin 4} (ha : a ≠ h) :
    ({p h, p a} : Finset V) ∈ (Finset.univ.image p).powersetCard 2 := by
  have ne : p h ≠ p a := fun e => ha (pi e.symm)
  refine Finset.mem_powersetCard.mpr ⟨?_, by simp [ne]⟩
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> simp

private theorem two_ports_in_heads (p : Fin 4 → V) (pi : Function.Injective p)
    {h a b : Fin 4} (ha : a ≠ h) (ab : a ≠ b) :
    ({p h, p a} : Finset V) ≠ {p h, p b} := by
  intro he
  have hm : p a ∈ ({p h, p b} : Finset V) := he ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.elim (fun e => ha (pi e)) (fun e => ab (pi e))

private theorem two_ports_represented_iff (p : Fin 4 → V) (pi : Function.Injective p)
    (Q : Finset V) {h a : Fin 4} (ha : a ≠ h) :
    ({p h, p a} : Finset V) ∈ representedPortPairs G (Finset.univ.image p) Q ↔
      ∃ v∈Q, G.Adj (p h) v ∧ G.Adj (p a) v := by
  rw [mem_representedPortPairs]
  have nc := (Finset.mem_powersetCard.mp (two_ports_in_image p pi ha)).2
  simp [nc, G.adj_comm]

/-- With exterior excess at least five, each port has actual exterior pair witnesses
with at least two distinct other port labels. The witnesses need not be distinct. -/
theorem high_excess_two_foreign_ports (h4 : FourCycleFree G)
    (p : Fin 4 → V) (pi : Function.Injective p) (Q : Finset V)
    (high : 5 ≤ portExcess G (Finset.univ.image p) Q) (h : Fin 4) :
    ∃ a b : Fin 4, a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      (∃ v∈Q, G.Adj (p h) v ∧ G.Adj (p a) v) ∧
      (∃ v∈Q, G.Adj (p h) v ∧ G.Adj (p b) v) := by
  classical
  let P := Finset.univ.image p
  let U := P.powersetCard 2
  let R := representedPortPairs G P Q
  let A := (Finset.univ : Finset (Fin 4)).erase h
  let Bad := A.filter fun a => ({p h, p a} : Finset V) ∉ R
  let Good := A.filter fun a => ({p h, p a} : Finset V) ∈ R
  have four : P.card = 4 := by simp [P, Finset.card_image_of_injective, pi]
  have six : U.card = 6 := by rw [show U = P.powersetCard 2 from rfl, Finset.card_powersetCard, four]; decide
  have five : 5 ≤ R.card := by
    rw [show R = representedPortPairs G P Q from rfl, represented_card h4]
    exact high.trans (portExcess_le_pair_weight P Q)
  have sub : R ⊆ U := by
    intro s hs
    obtain ⟨c,v,_,info⟩ := (mem_representedPortPairs P Q s).mp hs
    exact Finset.mem_powersetCard.mpr ⟨fun u hu => (info u hu).1, c⟩
  have lack : (U \ R).card ≤ 1 := by rw [Finset.card_sdiff sub, six]; omega
  have few : Bad.card ≤ 1 := by
    by_cases hh : 1 < Bad.card
    swap
    · omega
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp hh
    obtain ⟨ah,an⟩ := Finset.mem_filter.mp ha
    obtain ⟨bh,bn⟩ := Finset.mem_filter.mp hb
    have aNe := (Finset.mem_erase.mp ah).1
    have bNe := (Finset.mem_erase.mp bh).1
    exfalso
    exact (not_lt_of_ge lack) (Finset.one_lt_card.mpr
      ⟨_, Finset.mem_sdiff.mpr ⟨two_ports_in_image p pi aNe, an⟩,
       _, Finset.mem_sdiff.mpr ⟨two_ports_in_image p pi bNe, bn⟩,
       two_ports_in_heads p pi aNe ab⟩)
  have three : A.card = 3 := by simp [A]
  have partition : Good.card + Bad.card = A.card := by
    have d : Disjoint Good Bad := Finset.disjoint_left.mpr fun a hg hb =>
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hg).2
    have eq : Good ∪ Bad = A := Finset.filter_union_filter_neg_eq _ _
    rw [← Finset.card_union_of_disjoint d, eq]
  have many : 1 < Good.card := by omega
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp many
  obtain ⟨ah,ar⟩ := Finset.mem_filter.mp ha
  obtain ⟨bh,br⟩ := Finset.mem_filter.mp hb
  have aNe := (Finset.mem_erase.mp ah).1
  have bNe := (Finset.mem_erase.mp bh).1
  exact ⟨a,b,aNe,bNe,ab,(two_ports_represented_iff p pi Q aNe).mp ar,
    (two_ports_represented_iff p pi Q bNe).mp br⟩

/-- With exterior excess at least five, no inner core vertex can see any three
distinct ports. In particular every port is a good anchor. -/
theorem high_excess_every_anchor_without_triple_neighbor (h4 : FourCycleFree G)
    (p : Fin 4 → V) (pi : Function.Injective p) (Q D : Finset V)
    (dis : Disjoint Q D) (high : 5 ≤ portExcess G (Finset.univ.image p) Q) :
    ∀ i : Fin 4, ∀ v∈D, G.Adj (p i) v → ∀ j k : Fin 4, j≠i → k≠i → j≠k →
      ¬(G.Adj (p j) v ∧ G.Adj (p k) v) := by
  classical
  have four : (Finset.univ.image p).card = 4 := by simp [Finset.card_image_of_injective, pi]
  have bound := inner_pairs_at_most_one h4 _ Q D four dis high
  intro i v vd vi j k ji ki jk hyp
  have jR := (two_ports_represented_iff p pi D ji).mpr ⟨v,vd,vi,hyp.1⟩
  have kR := (two_ports_represented_iff p pi D ki).mpr ⟨v,vd,vi,hyp.2⟩
  exact (not_lt_of_ge bound) (Finset.one_lt_card.mpr ⟨_,jR,_,kR,two_ports_in_heads p pi ji jk⟩)

end Graffiti133FourPortPacking

#print axioms Graffiti133FourPortPacking.high_excess_two_foreign_ports
#print axioms Graffiti133FourPortPacking.high_excess_every_anchor_without_triple_neighbor
