import OddPatch180
import FirstForm180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem no_split {G : SimpleGraph V} {c : V} {S T : Finset V}
    (s : Split G c S T) (block : NoCut G) : False := by
  classical
  have proper (X : Finset V) (lt : X.card<Fintype.card V) : ∃ z,z∉X := by
    by_contra! h
    rw [eq_univ_iff_forall.mpr h,card_univ] at lt
    omega
  obtain ⟨a,at'⟩ := proper T s.smallR
  obtain ⟨b,bs⟩ := proper S s.smallL
  let W := ↥({c}ᶜ : Set V)
  let H := G.induce ({c}ᶜ : Set V)
  let i : W := ⟨a,fun e => at' (e ▸ s.both.2)⟩
  let j : W := ⟨b,fun e => bs (e ▸ s.both.1)⟩
  have go {v z : W} (p : H.Walk v z) : v.val∈S → z.val∈S := by
    induction p with
    | nil => exact id
    | @cons v t _ e _ ih =>
      intro vs
      apply ih
      rcases s.edges (show G.Adj v.val t.val from e) with k|k
      · exact k.2
      · exact (v.property (s.common vs k.1)).elim
  exact bs (go (block c i j).some ((s.either a).resolve_right at'))

/-- Any proper lower separation lies at the middle of the chord triangle.
The two tips are on opposite exclusive sides. -/
theorem chord_seam {J : SimpleGraph V} {c x y w : V} {S T : Finset V}
    (s : Split J c S T) (block : NoCut (J⊔edge x y)) (xw : J.Adj x w) (wy : J.Adj w y) :
    c=w ∧ ((x∈S ∧ x∉T ∧ y∈T ∧ y∉S) ∨ (x∈T ∧ x∉S ∧ y∈S ∧ y∉T)) := by
  classical
  have apart : ¬((x∈S ∧ y∈S) ∨ (x∈T ∧ y∈T)) := by
    intro both
    apply no_split (G:=J⊔edge x y) (c:=c) (S:=S) (T:=T) _ block
    refine ⟨s.cover,s.meet,?_,s.smallL,s.smallR⟩
    intro i j e
    rcases e with e|e
    · exact s.edges e
    rcases ((edge_adj ..).mp e).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact both
    · exact both.imp And.symm And.symm
  have sides := s.either x
  have tips := s.either y
  have xe := s.edges xw
  have ye := s.edges wy
  have seam : w∈S ∧ w∈T := by tauto
  exact ⟨(s.common seam.1 seam.2).symm,by tauto⟩

private theorem one_wing {J : SimpleGraph V} {x y w : V} {S T : Finset V}
    (s : Split J w S T) (xs : x∈S) (ys : y∉S) :
    side (J⊔edge x y) S=side J S ∧ Ports (J⊔edge x y) S x w := by
  constructor
  · ext i j
    constructor
    · rintro (e|e)
      · exact e
      rcases ((edge_adj ..).mp e).1 with ⟨_,h⟩|⟨h,_⟩
      · exact (ys (h ▸ j.property)).elim
      · exact (ys (h ▸ i.property)).elim
    · exact Or.inl
  · intro i hi j hj e
    rcases e with e|e
    · rcases s.edges e with a|b
      · exact (hj a.2).elim
      · exact Or.inr (s.common hi b.1)
    · rcases ((edge_adj ..).mp e).1 with ⟨h,_⟩|⟨_,h⟩
      · exact Or.inl h
      · exact (hj (h ▸ xs)).elim

/-- A lower wing of an upper rooted-sparse block is a block itself. A
wing on more than its two ports is nonbipartite in the lower graph. -/
theorem wing_odd {J : SimpleGraph V} (jc : J.Connected) {x y w r : V} {S T : Finset V}
    (s : Split J w S T) (xs : x∈S) (ys : y∉S) (xw : J.Adj x w)
    (block : NoCut (J⊔edge x y)) (sp : SparseAt (J⊔edge x y) r) :
    NoCut (side J S) ∧ (S={x,w} ∨ ¬TwoColor J S) := by
  classical
  let G := J⊔edge x y
  obtain ⟨eq,ports⟩ := one_wing s xs ys
  have con : (side G S).Connected := eq ▸ s.connectedL jc
  have noc := nocut_patch G block S x w xs s.both.1 (Or.inl xw) ports
  refine ⟨eq ▸ noc,?_⟩
  rcases sparse_block_odd_patch G (jc.mono le_sup_left) block r sp S x w xs s.both.1
    (Or.inl xw) ports con with h|bad
  · exact Or.inl h
  · right
    intro bip
    obtain ⟨f,hf⟩ := (color_function J S).mp bip
    apply bad
    apply (color_function G S).mpr
    refine ⟨f,?_⟩
    intro a ha b hb e
    have E : (side G S).Adj ⟨a,ha⟩ ⟨b,hb⟩ := e
    rw [eq] at E
    exact hf a ha b hb E

/-- Every maximum lower bipartite witness of a rank-dropping chord
contains the separating middle as well as the tips. -/
theorem locked_seam {J : SimpleGraph V} {x y w : V} {S T B : Finset V} (s : Split J w S T)
    (xs : x∈S) (ys : y∉S) (xy : x≠y) (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J)
    (top : MaxSet J B) : x∈B ∧ w∈B ∧ y∈B := by
  classical
  obtain ⟨c,hc⟩ := (color_function J B).mp top.1
  obtain ⟨xb,yb,_,path⟩ := rank_forces_route J x y xy drop B top c hc
  refine ⟨xb,?_,yb⟩
  by_contra wb
  have go {i j : V} (p : (within J B).Walk i j) : i∈S → j∈S := by
    induction p with
    | nil => exact id
    | @cons a b _ e _ ih =>
      intro aS
      apply ih
      rcases s.edges e.1 with h|h
      · exact h.2
      · exact (wb ((s.common aS h.1) ▸ e.2.1)).elim
  exact ys (go path.some xs)

#print axioms chord_seam
#print axioms wing_odd
#print axioms locked_seam
end Minimal180.OddBlock
