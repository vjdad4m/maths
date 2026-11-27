import BagCost180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem Bags.retained (h : Bags H G f) (S : Finset V) (keep : ∀ i,∃ x∈S,f x=i) :
    Bags (side H S) G (fun x : ↥S => f x.val) :=
  ⟨fun i => by obtain ⟨x,xs,eq⟩ := keep i; exact ⟨⟨x,xs⟩,eq⟩,fun ne => h.across ne⟩

omit [Fintype V] in
theorem Bags.metric (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B) (x y : V) :
    H.dist x y=if f x≠f y then G.dist (f x) (f y) else if x=y then 0 else if H.Adj x y then 1 else 2 := by
  classical
  split_ifs with diff same edge
  · let s (i : B) : V := if i=f x then x else if i=f y then y else (h.onto i).choose
    have sec : Function.LeftInverse f s := by
      intro i
      dsimp [s]; split_ifs with ex ey
      · exact ex.symm
      · exact ey.symm
      · exact (h.onto i).choose_spec
    simpa [s,diff.symm] using h.repDist gc s sec (f x) (f y)
  · subst y; exact dist_self
  · exact dist_eq_one_iff_adj.mpr edge
  · have eq : f x=f y := not_not.mp diff
    obtain ⟨j,xj⟩ := exists_adj G gc hn (f x)
    obtain ⟨z,zj⟩ := h.onto j
    have xz : H.Adj x z := h.edgeUp (by rwa [zj])
    have zy : H.Adj z y := h.edgeUp (by rw [zj,←eq]; exact xj.symm)
    have hc := h.connected gc hn
    have upper := hc.dist_triangle (u:=x) (v:=z) (w:=y)
    rw [dist_eq_one_iff_adj.mpr xz,dist_eq_one_iff_adj.mpr zy] at upper
    have no0 := mt hc.dist_eq_zero_iff.mp same
    have no1 := mt dist_eq_one_iff_adj.mp edge
    omega

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
theorem Bags.retainedDist (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (S : Finset V) (keep : ∀ i,∃ x∈S,f x=i) (x y : ↥S) : (side H S).dist x y=H.dist x.val y.val := by
  classical
  rw [(h.retained S keep).metric gc hn,h.metric gc hn]
  simp only [Subtype.ext_iff]
  rfl

/-- Restricting all bags while keeping them nonempty can only raise
the number of marked vertices which must be lost from the leaf score. -/
theorem Bags.retainedLoss (h : Bags H G f) (gc : G.Connected) (hn : 2<Fintype.card B)
    (nh : ∀ i,¬Universal G i) (S : Finset V) (keep : ∀ i,∃ x∈S,f x=i) (U : Finset V) :
    let R := pull (fun x : ↥S => x.val) U
    weightedLeaves (side H S) R+U.card≤weightedLeaves H U+R.card := by
  classical
  intro R
  let F := fullBags f U
  let K := fullBags (fun x : ↥S => f x.val) R
  have inc : F⊆K := by
    intro i m
    exact full_iff.mpr (fun x eq => mem_pull.mpr (full_iff.mp m _ eq))
  have upper := (h.retained S keep).costExact gc hn nh R
  have lower := h.costExact gc hn nh U
  change weightedLeaves (side H S) R+K.card=R.card+weightedLeaves G K at upper
  change weightedLeaves H U+F.card=U.card+weightedLeaves G F at lower
  have leaf := restrict_leaves G K F
  have cnt := card_sdiff_add_card_eq_card inc
  omega

#print axioms Bags.retainedDist
#print axioms Bags.retainedLoss
end Minimal180.Substitution
