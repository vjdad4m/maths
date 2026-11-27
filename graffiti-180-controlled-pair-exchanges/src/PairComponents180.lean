import Controlled180

set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [DecidableEq V]

/-- The returned vertex b must meet every retained component, except that the
component of y can meet it through the added chord and the old edge xb. -/
theorem pair_core_iff (J : SimpleGraph V) (R : Finset V) (x y b : V)
    (xy : x≠y) (bx : b≠x) (by' : b≠y) (br : b∉R) (xr : x∉R) (yr : y∈R)
    (no : ¬Dominates J R x) :
    Con (J⊔SimpleGraph.edge x y) (insert b (insert x R)) ↔
      ∀ a∈R,Dominates J (part J R a) b ∨ (J.Adj x b ∧ (within J R).Reachable a y) := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let Q := insert b (insert x R)
  have lift {t : V} (h : t∈R) : t∈Q := mem_insert_of_mem (mem_insert_of_mem h)
  have bQ : b∈Q := mem_insert_self .. 
  have xQ : x∈Q := mem_insert_of_mem (mem_insert_self ..)
  have add : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
  have only {t : V} (tr : t∈R) (e : G.Adj x t) : t=y := by
    rcases e with e|e
    · exact (no ⟨t,tr,e⟩).elim
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact h.2
      · exact (xy h.1).elim
  have onR {i j : V} (ir : i∈R) (jr : j∈R) (e : G.Adj i j) : J.Adj i j := by
    rcases e with e|e
    · exact e
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact (xr (h.1 ▸ ir)).elim
      · exact (xr (h.2 ▸ jr)).elim
  have onB {i : V} (e : G.Adj b i) : J.Adj b i := by
    rcases e with e|e
    · exact e
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact (bx h.1).elim
      · exact (by' h.1).elim
  constructor
  · intro conn a ar
    by_contra fail
    push_neg at fail
    let H := part J R a
    have notx : x∉H := fun h => xr ((mem_part ..).mp h).1
    have notb : b∉H := fun h => br ((mem_part ..).mp h).1
    let mark (i : V) := i∈H ∨ (i=x ∧ y∈H)
    have stay {i j : V} (jq : j∈Q) (edge : G.Adj i j) (mi : mark i) : mark j := by
      rcases mi with ih|⟨ix,yh⟩
      · obtain ⟨ir,ai⟩ := (mem_part ..).mp ih
        rcases mem_insert.mp jq with jb|jq'
        · have e : G.Adj b i := jb ▸ edge.symm
          exact (fail.1 ⟨i,ih,onB e⟩).elim
        rcases mem_insert.mp jq' with jx|jr
        · have e : G.Adj x i := jx ▸ edge.symm
          exact Or.inr ⟨jx,only ir e ▸ ih⟩
        · have e : (within J R).Adj i j := ⟨onR ir jr edge,ir,jr⟩
          exact Or.inl ((mem_part ..).mpr ⟨jr,ai.trans e.reachable⟩)
      · have e : G.Adj x j := ix ▸ edge
        rcases mem_insert.mp jq with jb|jq'
        · have exb : G.Adj x b := jb ▸ e
          exact (fail.2 (onB exb.symm).symm ((mem_part ..).mp yh).2).elim
        rcases mem_insert.mp jq' with jx|jr
        · exact Or.inr ⟨jx,yh⟩
        · exact Or.inl (only jr e ▸ yh)
    let f (i : V) := decide (mark i)
    have ok : OnEdges G Q f := fun i hi j hj e =>
      decide_eq_decide.mpr ⟨stay hj e,stay hi e.symm⟩
    have one : mark a := Or.inl ((mem_part ..).mpr ⟨ar,.refl _⟩)
    have zero : ¬mark b := fun h => h.elim notb (fun h' => bx h'.1)
    have eq := ((connected_cuts G Q).mp conn).2 f ok a (lift ar) b bQ
    simp [f,one,zero] at eq
  · intro hits
    apply (connected_cuts G Q).mpr
    refine ⟨⟨b,bQ⟩,?_⟩
    intro f edges
    have path {i j : V} (h : (within J R).Reachable i j) : f i=f j := by
      obtain ⟨p⟩ := h
      induction p with
      | nil => rfl
      | cons e _ ih => exact (edges _ (lift e.2.1) _ (lift e.2.2) (Or.inl e.1)).trans ih
    have anchors := edges x xQ y (lift yr) add
    have meet {a : V} (h : Dominates J (part J R a) b) : f a=f b := by
      obtain ⟨t,ht,bt⟩ := h
      obtain ⟨tr,at'⟩ := (mem_part ..).mp ht
      exact (path at').trans (edges t (lift tr) b bQ (Or.inl bt.symm))
    have root : f y=f b := by
      rcases hits y yr with h|⟨xb,_⟩
      · exact meet h
      · exact anchors.symm.trans (edges x xQ b bQ (Or.inl xb))
    have all (i : V) (hi : i∈Q) : f i=f b := by
      rcases mem_insert.mp hi with eq|hi'
      · rw [eq]
      rcases mem_insert.mp hi' with eq|hr
      · rw [eq]; exact anchors.trans root
      rcases hits i hr with h|⟨_,p⟩
      · exact meet h
      · exact (path p).trans root
    exact fun i hi j hj => (all i hi).trans (all j hj).symm

#print axioms pair_core_iff
end Minimal180.Controlled
