import CorePayment180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- Each nonempty fiber is an arbitrary graph. Distinct fibers are
completely joined precisely when their base vertices are adjacent. -/
structure Bags (H : SimpleGraph V) (G : SimpleGraph B) (f : V→B) : Prop where
  onto : Function.Surjective f
  across : ∀ {x y},f x≠f y → (H.Adj x y ↔ G.Adj (f x) (f y))

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem Bags.edgeUp (h : Bags H G f) {x y : V} (e : G.Adj (f x) (f y)) : H.Adj x y :=
  (h.across e.ne).mpr e

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
noncomputable def Bags.repHom (h : Bags H G f) (s : B→V) (sec : Function.LeftInverse f s) : G →g H :=
  ⟨s,fun {a b} e => h.edgeUp (by rwa [sec a,sec b])⟩

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem Bags.repDist (h : Bags H G f) (gc : G.Connected) (s : B→V) (sec : Function.LeftInverse f s)
    (a b : B) : H.dist (s a) (s b)=G.dist a b := by
  let em := h.repHom s sec
  obtain ⟨p,hp⟩ := gc.exists_walk_length_eq_dist a b
  let path := p.map em
  have upper := H.dist_le path
  have len : path.length=p.length := Walk.length_map em p
  change H.dist (s a) (s b)≤path.length at upper
  rw [len,hp] at upper
  have calcLow {x y : V} (w : H.Walk x y) : G.dist (f x) (f y)≤w.length := by
    induction w with
    | nil => simp [dist_self]
    | @cons x z y e w ih =>
      rw [Walk.length_cons]
      by_cases eq : f x=f z
      · rw [eq]; omega
      have tri := gc.dist_triangle (u:=f x) (v:=f z) (w:=f y)
      rw [dist_eq_one_iff_adj.mpr ((h.across eq).mp e)] at tri
      omega
  have reach : H.Reachable (s a) (s b) := path.reachable
  obtain ⟨w,ww⟩ := reach.exists_walk_length_eq_dist
  have low := calcLow w
  rw [sec a,sec b,ww] at low
  exact le_antisymm upper low

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
theorem Bags.connected (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B) : H.Connected := by
  classical
  let s (i : B) := (h.onto i).choose
  have sec : Function.LeftInverse f s := fun i => (h.onto i).choose_spec
  let em := h.repHom s sec
  obtain ⟨r⟩ := gc.nonempty
  apply (connected_iff_exists_forall_reachable H).mpr
  refine ⟨s r,fun x => ?_⟩
  obtain ⟨j,e⟩ := exists_adj G gc hn (f x)
  have edge : H.Adj x (s j) := h.edgeUp (by rwa [sec j])
  exact ((gc r j).map em).trans edge.symm.reachable

#print axioms Bags.repDist
#print axioms Bags.connected
end Minimal180.Substitution
