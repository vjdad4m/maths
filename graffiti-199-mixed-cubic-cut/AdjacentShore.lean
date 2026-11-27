import MixedSplice
import BridgeRoutes

namespace Graffiti199Depleted.Catalogue.CubicMixedCut

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] (F : CubicMixedCut G)

def leftOnly : Set V := {x | x ∈ F.inner ∧ G.Adj F.b x ∧ ¬ G.Adj F.c x}
def rightOnly : Set V := {x | x ∈ F.inner ∧ G.Adj F.c x ∧ ¬ G.Adj F.b x}
def hub : Set V := {x | x ∈ F.inner ∧ G.Adj F.b x ∧ G.Adj F.c x}
def leftBlock : Set V := {F.b} ∪ F.leftOnly
def rightBlock : Set V := {F.c} ∪ F.rightOnly

omit [Fintype V] in
theorem leftInB : F.leftBlock ⊆ F.B := by
  rintro x (eq|h)
  · exact (show x = F.b from eq).symm ▸ F.bB
  · exact h.1.1

omit [Fintype V] in
theorem rightInB : F.rightBlock ⊆ F.B := by
  rintro x (eq|h)
  · exact (show x = F.c from eq).symm ▸ F.cB
  · exact h.1.1

omit [Fintype V] in
theorem wingsApart : Disjoint F.leftBlock F.rightBlock := by
  apply Set.disjoint_left.mpr
  rintro x (e|a) (f|b)
  · exact F.bc ((show x = F.b from e).symm.trans (show x = F.c from f))
  · exact b.1.2.1 e
  · exact a.1.2.2 f
  · exact b.2.2 a.2.1

omit [Fintype V] in
theorem hubApart : Disjoint (F.leftBlock ∪ F.rightBlock) F.hub := by
  apply Set.disjoint_left.mpr
  rintro x ((e|l)|(e|r)) h
  · exact h.1.2.1 e
  · exact l.2.2 h.2.2
  · exact h.1.2.2 e
  · exact r.2.2 h.2.1

theorem blocks_cover (budget : treeNumber G ≤ 5) : (F.leftBlock ∪ F.rightBlock) ∪ F.hub = F.B := by
  ext x
  constructor
  · rintro ((h|h)|h)
    · exact F.leftInB h
    · exact F.rightInB h
    · exact h.1.1
  · intro h
    rcases F.split_B h with rfl|rfl|core
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inl rfl))
    · classical
      rcases F.dominates_inner budget core with bx|cx
      · by_cases cx : G.Adj F.c x
        · exact Or.inr ⟨core,bx,cx⟩
        · exact Or.inl (Or.inl (Or.inr ⟨core,bx,cx⟩))
      · by_cases bx : G.Adj F.b x
        · exact Or.inr ⟨core,bx,cx⟩
        · exact Or.inl (Or.inr (Or.inr ⟨core,cx,bx⟩))

theorem left_clique (budget : treeNumber G ≤ 5) : F.leftBlock.Pairwise G.Adj := by
  rintro x (xb|xi) y (yb|yi) xy
  · have eq : x = y := (show x = F.b from xb).trans (show y = F.b from yb).symm
    exact (xy eq).elim
  · exact (show x = F.b from xb).symm ▸ yi.2.1
  · exact (show y = F.b from yb).symm ▸ xi.2.1.symm
  · exact F.inner_adjacent_of_common_contact budget F.rb F.bB xi.1 yi.1 xy xi.2.1 yi.2.1

theorem right_clique (budget : treeNumber G ≤ 5) : F.rightBlock.Pairwise G.Adj := by
  rintro x (xc|xi) y (yc|yi) xy
  · have eq : x = y := (show x = F.c from xc).trans (show y = F.c from yc).symm
    exact (xy eq).elim
  · exact (show x = F.c from xc).symm ▸ yi.2.1
  · exact (show y = F.c from yc).symm ▸ xi.2.1.symm
  · exact F.inner_adjacent_of_common_contact budget F.rc F.cB xi.1 yi.1 xy xi.2.1 yi.2.1

theorem bridge_only (budget : treeNumber G ≤ 5) {x y : V}
    (xl : x ∈ F.leftBlock) (yr : y ∈ F.rightBlock) (xy : G.Adj x y) :
    x = F.b ∧ y = F.c := by
  rcases xl with xb|xi <;> rcases yr with yc|yi
  · exact ⟨xb,yc⟩
  · exact (yi.2.2 ((show x = F.b from xb) ▸ xy)).elim
  · exact (xi.2.2 ((show y = F.c from yc) ▸ xy.symm)).elim
  · exact (F.no_edge_between_exclusive budget xi.1 yi.1 xi.2.1 yi.2.2 xy).elim

theorem hub_universal (budget : treeNumber G ≤ 5) {x y : V}
    (xh : x ∈ F.hub) (yB : y ∈ F.B) (xy : x ≠ y) : G.Adj x y := by
  rcases F.split_B yB with rfl|rfl|yi
  · exact xh.2.1.symm
  · exact xh.2.2.symm
  · rcases F.dominates_inner budget yi with byEdge|cyEdge
    · exact F.inner_adjacent_of_common_contact budget F.rb F.bB xh.1 yi xy xh.2.1 byEdge
    · exact F.inner_adjacent_of_common_contact budget F.rc F.cB xh.1 yi xy xh.2.2 cyEdge

theorem some_exclusive (budget : treeNumber G ≤ 5) (bcEdge : G.Adj F.b F.c) :
    F.leftOnly.Nonempty ∨ F.rightOnly.Nonempty := by
  classical
  apply Classical.byContradiction
  intro no
  apply F.noncliqueB
  have split (x : V) (xB : x ∈ F.B) : x = F.b ∨ x = F.c ∨ x ∈ F.hub := by
    have h : x ∈ (F.leftBlock ∪ F.rightBlock) ∪ F.hub := (F.blocks_cover budget).symm ▸ xB
    rcases h with ((xb|xx)|(xc|xx))|xz
    · exact Or.inl xb
    · exact (no (Or.inl ⟨x,xx⟩)).elim
    · exact Or.inr (Or.inl xc)
    · exact (no (Or.inr ⟨x,xx⟩)).elim
    · exact Or.inr (Or.inr xz)
  intro x xB y yB xy
  rcases split x xB with rfl|rfl|xz
  · rcases split y yB with rfl|rfl|yz
    · exact (xy rfl).elim
    · exact bcEdge
    · exact yz.2.1
  · rcases split y yB with rfl|rfl|yz
    · exact bcEdge.symm
    · exact (xy rfl).elim
    · exact yz.2.2
  · exact F.hub_universal budget xz yB xy

def bridge (budget : treeNumber G ≤ 5) (bcEdge : G.Adj F.b F.c) : BridgedCliques G :=
  ⟨F.leftBlock,F.rightBlock,F.b,F.c,Or.inl rfl,Or.inl rfl,bcEdge,F.wingsApart,
    F.left_clique budget,F.right_clique budget⟩

#print axioms bridge_only
#print axioms hub_universal

end Graffiti199Depleted.Catalogue.CubicMixedCut
