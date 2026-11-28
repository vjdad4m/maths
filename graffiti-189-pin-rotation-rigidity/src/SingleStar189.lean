import LockedPins189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack
open private Graffiti189LongestPath.OneSlack.boundary_lower Graffiti189LongestPath.OneSlack.first_eq_if_no_pair
  Graffiti189LongestPath.OneSlack.cardinal_flankVertices Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.boundary_except_pins_two Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary from OneSlack189
open private Graffiti189LongestPath.OneSlack.MultiRotation.rigidity_of_tight
  Graffiti189LongestPath.OneSlack.MultiRotation.chord_forces_first_fringe from MultiPinRotation189
open private Graffiti189LongestPath.pin_data from SmallSeparator189
set_option warningAsError true
namespace Graffiti189LongestPath.SingleStar
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The one-pin branch has only one slot of flank slack. A point at
distance four necessarily exhausts it; a boundary larger than connectivity
also exhausts it. Both force a rigid pair of path flanks. -/
theorem singleton_star_budget (hc : G.Connected) (k : Nat)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (cap : (EvenFrom G x).card≤k+3) :
    let B := External G (OmittedStar p x)
    let F := DistanceTwo G x \ B
    k ≤ B.card ∧ B.card ≤ k+1 ∧ 2≤F.card ∧
      B.card+F.card+(Shell G x 4).card≤k+3 ∧
      ((Shell G x 4).Nonempty → B.card=k ∧ F=FlankVertices p x) ∧
      (B.card=k+1 → (Shell G x 4).card=0 ∧ F=FlankVertices p x) := by
  classical
  dsimp only
  let B := External G (OmittedStar p x)
  let F := DistanceTwo G x \ B
  have single : PairedPins p x=∅ := eq_empty_iff_forall_not_mem.mpr (by
    intro i hi
    obtain ⟨ii,j,jj,eq|eq⟩ := mem_filter.mp hi <;>
      have cc := one_lt_card.mpr ⟨i,ii,j,jj,by omega⟩ <;>
      omega)
  have first := Graffiti189LongestPath.OneSlack.first_eq_if_no_pair (p:=p) (x:=x) single
  have flank : (FlankVertices p x).card=2 := by
    rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices hp,flank_count_exact hp hx,first,one]
  have flsub := flanks_outside_boundary hc hp hx
  have l := card_le_card flsub
  have b := Graffiti189LongestPath.OneSlack.boundary_lower k hp hx conn
  have sides : Disjoint (B \ PinVertices p x) F := disjoint_left.mpr
    (fun _ l r => (mem_sdiff.mp r).2 (mem_sdiff.mp l).1)
  have sub := union_subset (Graffiti189LongestPath.OneSlack.boundary_except_pins_two hc hp hx)
      (sdiff_subset : F ⊆ DistanceTwo G x)
  have a := card_le_card sub
  have cs := card_sdiff_add_card_eq_card (Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx)
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,one] at cs
  rw [card_union_of_disjoint sides] at a
  have r := shell_two_four_le_of_even cap
  rw [shell_two] at r
  change (FlankVertices p x).card≤F.card at l
  change k≤B.card at b
  change (B\PinVertices p x).card+1=B.card at cs
  change (B\PinVertices p x).card+F.card≤(DistanceTwo G x).card at a
  have full : B.card+F.card+(Shell G x 4).card≤k+3 := by omega
  have rigid (small : F.card≤2) : F=FlankVertices p x := by
    apply (eq_of_subset_of_card_le flsub _).symm
    change F.card≤(FlankVertices p x).card
    omega
  change k ≤ B.card ∧ B.card ≤ k+1 ∧ 2≤F.card ∧
    B.card+F.card+(Shell G x 4).card≤k+3 ∧
    ((Shell G x 4).Nonempty → B.card=k ∧ F=FlankVertices p x) ∧
    (B.card=k+1 → (Shell G x 4).card=0 ∧ F=FlankVertices p x)
  refine ⟨b,by omega,by omega,full,?_ ,?_⟩
  · intro some
    have positive := card_pos.mpr some
    exact ⟨by omega,rigid (by omega)⟩
  · intro big
    exact ⟨by omega,rigid (by omega)⟩

theorem tight_singleton_start_locked (hc : G.Connected) (k : Nat)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (cap : (EvenFrom G x).card≤k+3)
    (tight : (Shell G x 4).Nonempty ∨ (External G (OmittedStar p x)).card=k+1)
    {i : Nat} (hi : i∈Pins p x) (ii : 2≤i) : ¬G.Adj a (p.getVert i) := by
  have h := singleton_star_budget hc k conn hp hx one cap
  have rigid : DistanceTwo G x \ External G (OmittedStar p x)=FlankVertices p x :=
    tight.elim (fun h' => (h.2.2.2.2.1 h').2) (fun h' => (h.2.2.2.2.2 h').2)
  have inner : ∀ j∈Pins p x, 2≤j := by
    intro j hj
    have eq : i=j := Classical.byContradiction (fun ne => by
      have nn := one_lt_card.mpr ⟨i,hi,j,hj,ne⟩
      omega)
    exact eq ▸ ii
  exact Graffiti189LongestPath.OneSlack.MultiRotation.chord_forces_first_fringe hc hp hx hi inner rigid
#print axioms singleton_star_budget
#print axioms tight_singleton_start_locked
end Graffiti189LongestPath.SingleStar
