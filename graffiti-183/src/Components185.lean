import Slices185

namespace Graffiti185.Cut
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Deleted (r : V) := G.induce ({r}ᶜ : Set V)

theorem bound_delete_components (r : V) (hc : G.Connected) :
    Fintype.card V + Nat.card (Deleted G r).ConnectedComponent ≤
      Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G := by
  classical
  let W : Set V := {r}ᶜ
  let H := G.induce W
  obtain ⟨v,hv⟩ := exists_ne r
  let w0 : W := ⟨v,hv⟩
  letI : Nonempty H.ConnectedComponent := ⟨H.connectedComponentMk w0⟩
  letI : Fintype H.ConnectedComponent :=
    Fintype.ofSurjective H.connectedComponentMk fun c =>
      c.ind (fun v => ⟨v,rfl⟩)
  let label (v : V) : H.ConnectedComponent :=
    if e : v ≠ r then H.connectedComponentMk ⟨v,e⟩ else H.connectedComponentMk w0
  have hsep (v w : V) (hv : v ≠ r) (hw : w ≠ r) (e : G.Adj v w) :
      label v = label w := by
    simp only [label,dif_pos hv,dif_pos hw]
    exact ConnectedComponent.sound ((show H.Adj ⟨v,hv⟩ ⟨w,hw⟩ from e).reachable)
  have hne (i : H.ConnectedComponent) : ∃ v, v ≠ r ∧ label v = i := by
    refine i.ind fun z => ?_
    have hz : z.val ≠ r := z.prop
    exact ⟨z.val,hz,by simp only [label,dif_pos hz]⟩
  simpa only [Deleted,Nat.card_eq_fintype_card] using bound_cut_label G r label hc hsep hne

theorem conjecture185_of_cut_three (r : V) (hc : G.Connected)
    (hk : 3 ≤ Nat.card (Deleted G r).ConnectedComponent) : Graffiti185.Claim185 G := by
  have b := bound_delete_components G r hc
  have bl := Graffiti185.Reuse.order_bound G hc
  by_contra failure
  rcases (Graffiti185.counterexample_iff_of_order_bound hc bl).mp failure with h | h
  · rcases h.2 with h | h <;> omega
  · omega

theorem failure_at_cut_two (r : V) (hc : G.Connected)
    (hk : 2 ≤ Nat.card (Deleted G r).ConnectedComponent)
    (hf : ¬Graffiti185.Claim185 G) :
    Nat.card (Deleted G r).ConnectedComponent = 2 ∧
      Graffiti185.squareMaxDegree G + 1 = Fintype.card V ∧
      Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G = Fintype.card V + 2 ∧
      (3 / 2 : ℚ) < Graffiti185.averageDistance (Graffiti185.square G) := by
  have b := bound_delete_components G r hc
  have bl := Graffiti185.Reuse.order_bound G hc
  rcases (Graffiti185.counterexample_iff_of_order_bound hc bl).mp hf with h | h
  · rcases h.2 with hl | ht
    · omega
    · exact ⟨by omega,h.1,ht.1,ht.2⟩
  · omega

#print axioms conjecture185_of_cut_three
#print axioms failure_at_cut_two
#print axioms bound_delete_components

end Graffiti185.Cut
