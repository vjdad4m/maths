import BagBlocks180
import BagLeaves180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- Indices all of whose vertices are marked. -/
noncomputable def fullBags (f : V→B) (U : Finset V) : Finset B := univ.filter (fun i => ∀ x,f x=i → x∈U)

theorem full_iff {U : Finset V} {i : B} : i∈fullBags f U ↔ ∀ x,f x=i → x∈U := by simp [fullBags]

omit [Fintype V] [DecidableEq V] [Fintype B] in
theorem Bags.coreDown (h : Bags H G f) (D : Finset V) (dc : Con H D) (dom : ∀ v∉D,Dominates H D v) :
    Con G (D.image f) ∧ ∀ i∉D.image f,Dominates G (D.image f) i := by
  classical
  let q (x : ↥D) : ↥(D.image f) := ⟨f x.val,mem_image_of_mem _ x.property⟩
  have z : Bags (H.induce (D : Set V)) (G.induce (D.image f : Set B)) q := by
    refine ⟨fun i => ?_,fun {x y} ne => h.across (fun eq => ne (Subtype.ext eq))⟩
    obtain ⟨x,xd,fx⟩ := mem_image.mp i.property
    exact ⟨⟨x,xd⟩,Subtype.ext fx⟩
  have ⟨x⟩ := dc.nonempty
  refine ⟨(G.induce (D.image f : Set B)).connected_iff.mpr ⟨z.preDown dc.preconnected,⟨q x⟩⟩,?_⟩
  intro i out
  obtain ⟨v,rfl⟩ := h.onto i
  obtain ⟨y,yd,vy⟩ := dom v (fun m => out (mem_image_of_mem _ m))
  have ne : f v≠f y := fun eq => out (eq ▸ mem_image_of_mem _ yd)
  exact ⟨f y,mem_image_of_mem _ yd,(h.across ne).mp vy⟩

/-- A quotient bounds the loss of marked leaves from below, with
arbitrary edges in every bag. -/
theorem Bags.costLower (h : Bags H G f) (hc : H.Connected) (hn : 2<Fintype.card V) (U : Finset V) :
    weightedLeaves H U+(fullBags f U).card≤U.card+weightedLeaves G (fullBags f U) := by
  classical
  obtain ⟨K,ks,kt,opt⟩ := tree_opt H hc U
  let L := U∩leaves K
  let D := univ\L
  let F := fullBags f U
  have ⟨dc,dom⟩ := leaf_core H K ks kt hn L inter_subset_right
  have ⟨con,cov⟩ := h.coreDown D dc (fun v m => dom v (by simpa [D] using m))
  have lw := weightedCore G (D.image f) F con cov
  have inc : F∩D.image f⊆(U∩D).image f := by
    intro i m
    obtain ⟨x,xd,fx⟩ := mem_image.mp (mem_inter.mp m).2
    exact mem_image.mpr ⟨x,mem_inter.mpr ⟨full_iff.mp (mem_inter.mp m).1 x fx,xd⟩,fx⟩
  have cap := (card_le_card inc).trans card_image_le
  have split := card_sdiff_add_card_inter F (D.image f)
  have old : U∩D=U\L := by ext x; simp [D]
  rw [old] at cap
  have sz := card_sdiff_add_card_eq_card (show L⊆U from inter_subset_left)
  change L.card=weightedLeaves H U at opt
  change weightedLeaves H U+F.card≤U.card+weightedLeaves G F
  omega

/-- Exact loss of eligible leaves through arbitrary bags when the base
has no universal vertex. The identity depends only on the fully marked
bags and holds with any internal edges, weights zero or one. -/
theorem Bags.costExact (h : Bags H G f) (gc : G.Connected) (hn : 2<Fintype.card B)
    (nh : ∀ i,¬Universal G i) (U : Finset V) :
    weightedLeaves H U+(fullBags f U).card=U.card+weightedLeaves G (fullBags f U) := by
  classical
  have upper := Fintype.card_le_of_surjective f h.onto
  apply le_antisymm (h.costLower (h.connected gc (by omega)) (by omega) U)
  let F := fullBags f U
  have pick (i : B) : ∃ x,f x=i ∧ (x∈U ↔ i∈F) := by
    by_cases yes : i∈F
    · obtain ⟨x,fx⟩ := h.onto i
      exact ⟨x,fx,iff_of_true (full_iff.mp yes _ fx) yes⟩
    · have miss : ∃ x,f x=i ∧ x∉U := by
        by_contra! all
        exact yes (full_iff.mpr all)
      obtain ⟨x,fx,out⟩ := miss
      exact ⟨x,fx,iff_of_false out yes⟩
  choose s sec mark using pick
  have left : Function.LeftInverse f s := sec
  have pull_eq : pull s U=F := by ext i; exact mem_pull.trans (mark i)
  have cnt := section_count s left.injective U
  have lf := h.liftLeaves gc hn nh s left U
  rw [pull_eq] at cnt lf
  change U.card+weightedLeaves G F≤weightedLeaves H U+F.card
  omega

#print axioms Bags.coreDown
#print axioms Bags.costLower
#print axioms Bags.costExact
end Minimal180.Substitution
