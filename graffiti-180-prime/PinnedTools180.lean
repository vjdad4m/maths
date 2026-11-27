import PinnedEquivalent180
import PruneMarks180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B W : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem Bags.compose {J : SimpleGraph W} {q : B→W} (h : Bags H G f) (g : Bags G J q) :
    Bags H J (q∘f) :=
  ⟨g.onto.comp h.onto,fun ne => (h.across (fun eq => ne (congrArg q eq))).trans (g.across ne)⟩

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem Bags.domLift (h : Bags H G f) {r y : V} (d : DomEdge G (f r) (f y)) : DomEdge H r y := by
  refine ⟨h.edgeUp d.1,fun x _ _ => ?_⟩
  by_cases a : f x=f r
  · exact Or.inr (h.edgeUp (a ▸ d.1))
  by_cases b : f x=f y
  · exact Or.inl (h.edgeUp (b ▸ d.1.symm))
  exact (d.2 _ a b).imp h.edgeUp h.edgeUp

theorem dominating_pins (H : SimpleGraph V) (hc : H.Connected) (hn : 2<Fintype.card V)
    {r y : V} (d : DomEdge H r y) (p : Bool) (A : Finset V) (ai : Indep H A) :
    Pinned H r p A (A∩parity H r p) := by
  classical
  let D := A∩parity H r p
  let h := force_bags H D
  have du : DomEdge (force H D) (.inl r) (.inl y) := h.domLift d
  have count := Fintype.card_le_of_surjective _ h.onto
  apply forced_witness H hc hn A D ai r p Subset.rfl
  exact dom_edge_rooted _ (h.connected hc (by omega)) (by omega) du p

omit [DecidableEq B] in
theorem pin_nohub (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B) (high : 2<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep H A) (bad : ¬Pinned H r p A (A∩parity H r p)) :
    ∀ i,¬Universal G i := by
  intro i hub
  obtain ⟨_,ed⟩ := h.hubEdge gc hn hub r
  exact bad (dominating_pins H (h.connected gc hn) high ed p A ai)

omit [Fintype V] in
theorem push_color (H : SimpleGraph V) (S : Finset V) {Z : Finset ↥S} (c : TwoColor (side H S) Z) :
    TwoColor H (push Z) := by
  classical
  obtain ⟨col,good⟩ := (color_function ..).mp c
  apply (color_function ..).mpr
  let paint (x : V) := if m : x∈S then col ⟨x,m⟩ else false
  refine ⟨paint,fun x xm y ym edge => ?_⟩
  have xs := push_sub Z xm
  have ys := push_sub Z ym
  simpa [paint,xs,ys] using good ⟨x,xs⟩ ((in_push _).mp xm) ⟨y,ys⟩ ((in_push _).mp ym) edge

/-- Independent twins have identical open neighborhoods. -/
def FalseTwins (H : SimpleGraph V) (x y : V) : Prop := x≠y ∧ ∀ z,H.Adj x z ↔ H.Adj y z

omit [Fintype V] in
theorem FalseTwins.paint {x y : V} (tw : FalseTwins H x y) {Z : Finset V} (col : TwoColor H Z) (ym : y∈Z) :
    TwoColor H (insert x Z) := by
  classical
  obtain ⟨c,ok⟩ := (color_function ..).mp col
  let d (z : V) := if z=x then c y else c z
  apply (color_function ..).mpr
  refine ⟨d,fun a am b bm e => ?_⟩
  by_cases ax : a=x <;> by_cases bx : b=x
  · exact (e.ne (ax.trans bx.symm)).elim
  · have edge := (tw.2 b).mp (ax ▸ e)
    simpa [d,ax,bx] using ok y ym b ((mem_insert.mp bm).resolve_left bx) edge
  · have edge := (tw.2 a).mp (bx ▸ e.symm)
    simpa [d,ax,bx] using ok a ((mem_insert.mp am).resolve_left ax) y ym edge.symm
  · simpa [d,ax,bx] using ok a ((mem_insert.mp am).resolve_left ax) b ((mem_insert.mp bm).resolve_left bx) e

omit [DecidableEq B] in
theorem pulled_mark (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (S : Finset V) (keep : ∀ i,∃ x∈S,f x=i) (r : ↥S) (p : Bool) (A : Finset V) :
    let R := pull (fun x : ↥S => x.val)
    let P := parity H r.val p
    let Q := parity (side H S) r p
    Q=R P ∧ eligible (R A) Q r=R (eligible A P r.val) := by
  intro R P Q
  have pp : Q=R P := by ext x; simp only [Q,R,P,mem_pull,mem_parity,h.retainedDist gc hn S keep x r]
  refine ⟨pp,?_⟩
  rw [pp]
  ext x; simp only [R,mem_pull,eligible_iff]; simp [Subtype.ext_iff]

#print axioms dominating_pins
#print axioms pin_nohub
#print axioms FalseTwins.paint
#print axioms pulled_mark
end Minimal180.Substitution
