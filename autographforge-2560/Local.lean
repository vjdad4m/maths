import Patterns

namespace BullCover1125
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} {a b : V} {X : Finset V}

/-- The outside vertices adjacent to the ends of a selected edge. -/
structure Attached (G : SimpleGraph V) (a b : V) (X : Finset V) : Prop where
  edge : G.Adj a b
  away : ∀ x ∈ X, x ≠ a ∧ x ≠ b
  independent : ∀ x ∈ X, ∀ y ∈ X, ¬ G.Adj x y
  touch : ∀ x ∈ X, G.Adj a x ∨ G.Adj b x

/-- Two outside vertices can always be paired with different endpoints.
Otherwise both see only the same endpoint, whose other endpoint makes a claw. -/
theorem pair_up (cl : Free G claw) (h : Attached G a b X) {x y}
    (hx : x ∈ X) (hy : y ∈ X) (ne : x ≠ y) :
    (G.Adj a x ∧ G.Adj b y) ∨ (G.Adj a y ∧ G.Adj b x) := by
  have atA (ax : G.Adj a x) (ay : G.Adj a y) : G.Adj b x ∨ G.Adj b y := by
    have z := claw_neighbors cl h.edge ax ay (h.away x hx).2.symm (h.away y hy).2.symm ne
    exact z.elim Or.inl (fun t => Or.inr (t.resolve_right (h.independent x hx y hy)))
  have atB (bx : G.Adj b x) (by' : G.Adj b y) : G.Adj a x ∨ G.Adj a y := by
    have z := claw_neighbors cl h.edge.symm bx by' (h.away x hx).1.symm (h.away y hy).1.symm ne
    exact z.elim Or.inl (fun t => Or.inr (t.resolve_right (h.independent x hx y hy)))
  have tx := h.touch x hx
  have ty := h.touch y hy
  tauto

/-- If there are three outside vertices, neither endpoint sees them all.
There must be a private neighbor on each side, and a third vertex sees both
endpoints by the pairing lemma. The resulting five vertices induce a bull. -/
theorem at_most_two (cl : Free G claw) (bu : Free G bull) (h : Attached G a b X) :
    X.card ≤ 2 := by
  classical
  by_contra! large
  obtain ⟨r,s,t,hr,hs,ht,rs,rt,st⟩ := two_lt_card_iff.mp large
  have missing (v : V) : ∃ z ∈ X, ¬ G.Adj v z := by
    by_contra! all
    have z := claw_neighbors cl (all r hr) (all s hs) (all t ht) rs rt st
    exact z.elim (h.independent r hr s hs)
      (fun e => e.elim (h.independent r hr t ht) (h.independent s hs t ht))
  obtain ⟨x,hx,bx⟩ := missing b
  obtain ⟨y,hy,ay⟩ := missing a
  have ax := (h.touch x hx).resolve_right bx
  have by' := (h.touch y hy).resolve_left ay
  have third : ∃ z ∈ X, z ≠ x ∧ z ≠ y := by
    by_contra! no
    have sub : X ⊆ {x,y} := fun v hv => by
      by_cases eq : v=x
      · simp [eq]
      · simp [no v hv eq]
    have cap := (card_le_card sub).trans (card_insert_le x {y})
    simp at cap
    omega
  obtain ⟨z,hz,zx,zy⟩ := third
  have bz := ((pair_up cl h hx hz zx.symm).resolve_right (fun e => bx e.2)).2
  have az := ((pair_up cl h hy hz zy.symm).resolve_left (fun e => ay e.1)).1
  exact bull_pattern bu h.edge ax by' az bz bx ay (h.independent x hx y hy)
    (h.independent x hx z hz) (h.independent y hy z hz)

/-- Two edges cover the selected edge's endpoints together with every
outside vertex attached to it. Overlap with other pieces is harmless. -/
theorem small_piece (cl : Free G claw) (h : Attached G a b X) (small : X.card ≤ 2) :
    ∃ P : Finset G.edgeSet, P.card ≤ 2 ∧
      ∀ v, v=a ∨ v=b ∨ v∈X → ∃ e ∈ P, v ∈ e.val := by
  classical
  let edge {u v : V} (uv : G.Adj u v) : G.edgeSet := ⟨s(u,v),uv⟩
  have left {u v : V} (uv : G.Adj u v) : u ∈ (edge uv).val := Sym2.mem_iff.mpr (Or.inl rfl)
  have right {u v : V} (uv : G.Adj u v) : v ∈ (edge uv).val := Sym2.mem_iff.mpr (Or.inr rfl)
  by_cases two : X.card = 2
  · obtain ⟨x,y,ne,eq⟩ := card_eq_two.mp two
    have hx : x ∈ X := by simp [eq]
    have hy : y ∈ X := by simp [eq]
    have make {s t : V} (as' : G.Adj a s) (bt : G.Adj b t) (all : ∀ v ∈ X, v=s ∨ v=t) :
        ∃ P : Finset G.edgeSet, P.card ≤ 2 ∧
          ∀ v, v=a ∨ v=b ∨ v∈X → ∃ e ∈ P, v ∈ e.val := by
      refine ⟨{edge as',edge bt},(card_insert_le _ _).trans (by simp),?_⟩
      rintro v (rfl|rfl|hv)
      · exact ⟨edge as',by simp,left _⟩
      · exact ⟨edge bt,by simp,left _⟩
      · rcases all v hv with rfl|rfl
        · exact ⟨edge as',by simp,right _⟩
        · exact ⟨edge bt,by simp,right _⟩
    rcases pair_up cl h hx hy ne with ⟨ax,by'⟩|⟨ay,bx⟩
    · exact make ax by' (by simp [eq])
    · exact make ay bx (by simp [eq,or_comm])
  · by_cases one : X.card = 1
    · obtain ⟨x,eq⟩ := card_eq_one.mp one
      have hx : x ∈ X := by simp [eq]
      have incident : ∃ e : G.edgeSet, x ∈ e.val := by
        rcases h.touch x hx with ax|bx
        · exact ⟨edge ax,right _⟩
        · exact ⟨edge bx,right _⟩
      obtain ⟨f,hf⟩ := incident
      refine ⟨{edge h.edge,f},(card_insert_le _ _).trans (by simp),?_⟩
      rintro v (rfl|rfl|hv)
      · exact ⟨edge h.edge,by simp,left _⟩
      · exact ⟨edge h.edge,by simp,right _⟩
      · have same : v=x := by simpa [eq] using hv
        exact ⟨f,by simp,same ▸ hf⟩
    · have empty : X = ∅ := card_eq_zero.mp (by omega)
      refine ⟨{edge h.edge},by simp,?_⟩
      rintro v (rfl|rfl|hv)
      · exact ⟨edge h.edge,by simp,left _⟩
      · exact ⟨edge h.edge,by simp,right _⟩
      · simp [empty] at hv

theorem local_cover (cl : Free G claw) (bu : Free G bull) (h : Attached G a b X) :
    ∃ P : Finset G.edgeSet, P.card ≤ 2 ∧
      ∀ v, v=a ∨ v=b ∨ v∈X → ∃ e ∈ P, v ∈ e.val :=
  small_piece cl h (at_most_two cl bu h)

end BullCover1125
