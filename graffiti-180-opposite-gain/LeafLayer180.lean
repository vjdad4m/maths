import TwoPortRegions180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem two_neighbors (G : SimpleGraph V) {v x y : V} (ex : G.Adj v x) (ey : G.Adj v y) (xy : x≠y) : 2≤G.degree v := by
  have sub : ({x,y}:Finset V)⊆G.neighborFinset v := insert_subset ((G.mem_neighborFinset ..).mpr ex)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ey))
  have h := card_le_card sub;simpa only [card_pair xy,card_neighborFinset_eq_degree] using h

/-- A nonroot vertex incident to a horizontal or ascending edge is not a leaf. -/
theorem forward_degree (G : SimpleGraph V) (gc : G.Connected) (r v x : V) (vr : v≠r) (ed : G.Adj v x)
    (dx : G.dist v r≤G.dist x r) : 2≤G.degree v := by
  obtain ⟨y,ev,dy⟩ := Graffiti169.exists_predecessor G gc r v vr
  exact two_neighbors G ed ev (fun eq => by rw [←eq] at dy;omega)

/-- A connected region meeting a lower layer cannot supply a contact
of b at its layer or higher if all its vertices at b's layer are leaves.
The contact itself may be a leaf. -/
theorem lower_contact (G : SimpleGraph V) (gc : G.Connected) (r b z : V) (S : Finset V)
    (con : Con G S) (zs : z∈S) (low : G.dist z r<G.dist b r)
    (thin : ∀ y∈S,G.dist y r=G.dist b r → G.degree y≤1) :
    ∀ x∈S,G.Adj b x → G.dist x r<G.dist b r := by
  classical
  let d (x : V) := G.dist x r
  let lower (x : V) := d x<d b ∨ (d x=d b ∧ ∃ u,G.Adj x u ∧ d u<d b)
  have step {x y : V} (xs : x∈S) (ed : G.Adj x y) (lx : lower x) : lower y := by
    rcases lx with lt|⟨eq,u,xu,lu⟩
    · have near := gc.dist_triangle (u:=y) (v:=x) (w:=r)
      rw [dist_eq_one_iff_adj.mpr ed.symm] at near
      change d y≤1+d x at near
      by_cases by' : d y<d b
      · exact Or.inl by'
      · exact Or.inr ⟨by omega,x,ed.symm,lt⟩
    · have small := thin x xs eq
      have ey : y=u := by by_contra ne;have := two_neighbors G ed xu ne;omega
      exact Or.inl (ey ▸ lu)
  let f (x : V) := decide (lower x)
  have stable : OnEdges G S f := fun x xs y ys ed => decide_eq_decide.mpr ⟨step xs ed,step ys ed.symm⟩
  intro x xs ed
  have eq := ((connected_cuts G S).mp con).2 f stable z zs x xs
  have yes : f z=true := decide_eq_true (Or.inl low : lower z)
  have got : lower x := of_decide_eq_true (eq.symm.trans yes : f x=true)
  rcases got with lt|⟨ex,u,xu,lu⟩
  · exact lt
  · have small := thin x xs ex
    have neq : b≠u := fun q => (q ▸ lu).false
    have := two_neighbors G ed.symm xu neq;omega

#print axioms two_neighbors
#print axioms forward_degree
#print axioms lower_contact
end Minimal180.OppositeGain
