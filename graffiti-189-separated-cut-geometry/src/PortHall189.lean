import WideWing189
import Mathlib.Combinatorics.Hall.Finite
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open private Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar
  Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
open Graffiti189LongestPath.OneSlack
set_option warningAsError true
namespace Graffiti189LongestPath.PortHall
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- At an exact connectivity cut, the entire boundary can be assigned distinct
neighbors on a sufficiently large shore. -/
theorem ports_match_into_shore (k : Nat) (A B : Finset V)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (dis : Disjoint A B) (exactB : B.card=k) (large : k≤A.card)
    {z : V} (za : z∉A) (zb : z∉B)
    (boundary : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B) :
    ∃ f : ↥(B : Set V) → V, Function.Injective f ∧ ∀ b, f b ∈ A ∧ G.Adj b.val (f b) := by
  classical
  let J (b : ↥(B : Set V)) := A.filter (G.Adj b.val)
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' J).mp (by
    intro T
    let N := T.biUnion J
    let S := T.image (fun b => b.val)
    have sub : S⊆B := by
      intro v hv
      obtain ⟨u,_,rfl⟩ := mem_image.mp hv
      exact u.property
    have sizeS : S.card=T.card := card_image_of_injective T Subtype.val_injective
    change T.card≤N.card
    apply Nat.le_of_not_gt
    intro fail
    have Nsub : N⊆A := by
      intro n hn
      obtain ⟨b,_,nb⟩ := mem_biUnion.mp hn
      exact (mem_filter.mp nb).1
    have ex : (A\N).Nonempty := by
      apply card_pos.mp
      have sa := card_le_card sub
      have hd := card_sdiff_add_card_eq_card Nsub
      omega
    obtain ⟨x,hx⟩ := ex
    let C := (B\S)∪N
    have za' : z∉A\N := fun h => za (mem_sdiff.mp h).1
    have zc : z∉C := fun h => (mem_union.mp h).elim (fun e => zb (mem_sdiff.mp e).1)
      (fun h => za (Nsub h))
    have dis' : Disjoint (A\N) C := disjoint_left.mpr (by
      intro u hu hv
      exact (mem_union.mp hv).elim
        (fun e => disjoint_left.mp dis (mem_sdiff.mp hu).1 (mem_sdiff.mp e).1)
        (mem_sdiff.mp hu).2)
    have bound : ∀ u∈A\N,∀ v∉A\N,G.Adj u v → v∈C := by
      intro u hu v hv e
      by_cases hA : v∈A
      · have vn : v∈N := Classical.byContradiction (fun nh => hv (mem_sdiff.mpr ⟨hA,nh⟩))
        exact mem_union.mpr (Or.inr vn)
      have bv := boundary u (mem_sdiff.mp hu).1 v hA e
      by_cases hS : v∈S
      · obtain ⟨w,hw,he⟩ := mem_image.mp hS
        exact ((mem_sdiff.mp hu).2 (mem_biUnion.mpr
          ⟨w,hw,mem_filter.mpr ⟨(mem_sdiff.mp hu).1,he.symm ▸ e.symm⟩⟩)).elim
      · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨bv,hS⟩))
    have c := Graffiti189LongestPath.boundary_card_of_connectivity k conn hx za' zc dis' bound
    have u := card_union_le (B\S) N
    have ch := card_sdiff_add_card_eq_card sub
    change k≤((B\S)∪N).card at c
    omega)
  exact ⟨f,inj,fun b => mem_filter.mp (mem b)⟩
#print axioms ports_match_into_shore


/-- All k ports of the exact star boundary admit simultaneous distinct
attachments to omitted vertices, not just the two ports adjacent to x. -/
theorem separated_double_port_matching (hc : G.Connected) (k : Nat)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (dy : y∉p.support) (xy : G.Adj x y)
    (high : k+2≤G.degree x) (cap : (EvenFrom G x).card≤k+3)
    (two : (Pins p x).card=2) (sep : PairedPins p x=∅) :
    ∃ f : ↥(External G (OmittedStar p x) : Set V) → V,
      Function.Injective f ∧ ∀ b, f b ∈ OmittedStar p x ∧ G.Adj b.val (f b) := by
  classical
  let A := OmittedStar p x
  let B := External G A
  obtain ⟨_,_,exactB⟩ := double_porter_saturated_one_slack hc k hp hx two cap conn dy xy
  have bcard : B.card=k := by
    rcases exactB with h|h
    · exact h.2
    · simp [sep] at h
  have xx : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have large : k≤A.card := by
    have sub : G.neighborFinset x ⊆ PinVertices p x ∪ A.erase x := by
      intro v hv
      have ed := (G.mem_neighborFinset x v).mp hv
      by_cases ons : v∈p.support
      · obtain ⟨i,hi,e⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx ons ed
        exact mem_union.mpr (Or.inl (mem_image.mpr ⟨i,hi,e⟩))
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨ed.ne.symm,
          Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨ons,Or.inr ed⟩⟩))
    have cd := card_le_card sub
    have cu := card_union_le (PinVertices p x) (A.erase x)
    rw [G.card_neighborFinset_eq_degree] at cd
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,two,card_erase_of_mem xx] at cu
    omega
  have na : a∉A := fun e => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp e).1 p.start_mem_support
  have nb : a∉B := by
    intro e
    obtain ⟨_,u,hu,ua⟩ := Graffiti189LongestPath.Rigidity.mem_external.mp e
    have off := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp hu).1
    exact (Graffiti189LongestPath.no_endpoints hp off).1 ua
  exact ports_match_into_shore k A B conn
    (disjoint_left.mpr (fun _ ha hb => (Graffiti189LongestPath.Rigidity.mem_external.mp hb).1 ha))
    bcard large na nb (fun _ hu _ hv e =>
      Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hv,_,hu,e⟩)
#print axioms separated_double_port_matching
end Graffiti189LongestPath.PortHall
