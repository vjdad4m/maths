import FiveEarTable
namespace Graffiti384b.OddStars.RichBlockFinish
open Finset SimpleGraph PositivePalette EarPacking CollisionBlock RichBlockModel
open private Prune.links from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a closed block of five rich vertices, a center in four internal
triangles is adjacent to all four other vertices of the block. -/
theorem universal_of_four {C : Finset V} (comp : Closed G C) (size : C.card=5)
    {v : V} (vm : v∈C) (many : 4≤EarTriangleLoss.inside G v) :
    ∀w∈C,w≠v → G.Adj v w := by
  classical
  let A := (C.erase v).filter (G.Adj v)
  have sub : internalPairs G v⊆A.powersetCard 2 := by
    intro p pm
    obtain ⟨ps,sz⟩ := mem_powersetCard.mp (pairs_subset G comp vm pm)
    obtain ⟨pl,_⟩ := mem_filter.mp pm
    have ns := (mem_powersetCard.mp (mem_filter.mp pl).1).1
    exact mem_powersetCard.mpr ⟨fun w wm => mem_filter.mpr ⟨ps wm,
      (((patch G ∅).mem_neighborFinset ..).mp (ns wm)).1⟩,sz⟩
  have ct := card_le_card sub
  rw [card_powersetCard] at ct
  change EarTriangleLoss.inside G v≤A.card.choose 2 at ct
  have big : 4≤A.card := by
    by_contra! small
    have h := Nat.choose_le_choose 2 (show A.card≤3 by omega)
    have num : Nat.choose 3 2=3 := by decide
    omega
  have er := card_erase_add_one vm
  have eq : A=C.erase v := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  intro w wm ne
  exact (mem_filter.mp (show w∈A from eq ▸ mem_erase.mpr ⟨ne,wm⟩)).2

theorem six_required (bad : bound G<gamma G) {C : Finset V} (comp : Closed G C)
    (nontrivial : 2≤C.card) : 6≤C.card := by
  classical
  have five := five_required G bad comp nontrivial
  by_contra! small
  have size : C.card=5 := by omega
  have top : ∃v∈C,4≤EarTriangleLoss.inside G v := by
    by_contra! no
    have ct := interval_capacity G bad comp.rich (lo:=2) (hi:=5) (fun v vm =>
      ⟨(mem_filter.mp (comp.rich vm)).2,by have a := no v vm; have b := EarTriangleLoss.loss_at_most_two G bad v; omega⟩)
    omega
  obtain ⟨v,vm,large⟩ := top
  let x : C := ⟨v,vm⟩
  let start := (Fintype.equivFinOfCardEq (show Fintype.card C=5 by simpa using size)).symm
  let e : Fin 5 ≃ C := (Equiv.swap 0 (start.symm x)).trans start
  have zero : e 0=x := by simp [e]
  let H := model G e
  have root (i : Fin 5) (ne : i≠0) : H.Adj 0 i := by
    change G.Adj (e 0).val (e i).val
    rw [zero]
    exact universal_of_four G comp size vm large _ (e i).2 (fun h => ne (e.injective ((Subtype.ext h).trans zero.symm)))
  let q := FiveEarTable.encode H
  have raw : FiveEarTable.graph q=H := FiveEarTable.encode_graph H root
  obtain ⟨p,fixed,k,isom⟩ := FiveEarTable.normalized q
  let lab := p.trans e
  have board : model G lab=FiveEarTable.graph (FiveEarTable.kind k) := by
    ext i j
    change H.Adj (p i) (p j) ↔ _
    rw [←raw]; exact isom i j
  obtain ⟨d,ok⟩ := feasible G bad comp (by omega) lab
  have sc := score G comp lab 0
  have eq : lab 0=x := by change e (p 0)=x; rw [fixed,zero]
  rw [eq] at sc
  have ⟨allowed,topscore⟩ := FiveEarTable.transport board d ok (sc ▸ large)
  exact FiveEarTable.impossible_kind k topscore d allowed

/-- A nontrivial component on which the largest and smallest internal
triangle counts differ by at most two suffices in every ambient order. -/
theorem exact_of_span_two {C : Finset V} (comp : Closed G C) (nontrivial : 2≤C.card)
    (k : ℕ) (range : ∀v∈C,k≤EarTriangleLoss.inside G v ∧ EarTriangleLoss.inside G v≤k+2) :
    gamma G≤bound G := by
  by_contra! bad
  have need := six_required G bad comp nontrivial
  have actual (v : V) (vm : v∈C) : k≤trianglesAt G v ∧ trianglesAt G v≤k+4 := by
    have h := range v vm; have a := CollisionPalette.add_loss G (comp.rich vm)
    have b := EarTriangleLoss.loss_at_most_two G bad v; omega
  have cap := interval_capacity G bad comp.rich actual
  omega

/-- All connected graphs in the catalogue range whose induced rich graph
has at most three internal triangle-count types satisfy the conjecture. -/
theorem exact_of_three_internal_types (conn : G.Connected) (ord : 2<Fintype.card V)
    (few : (CollisionPalette.palette G).card≤3) : gamma G≤bound G := by
  classical
  by_contra! bad
  have one : 1∈types G := by
    by_contra absent
    exact (Nat.not_le_of_gt bad) (MissingOne.exact G conn ord absent)
  obtain ⟨upper,odd⟩ := CollisionPalette.diversity G bad one
  have types_cap : (types G).card≤7 := by
    by_cases three : (CollisionPalette.palette G).card=3
    · have pos := odd (by omega)
      omega
    · omega
  have count := rich_count G bad one
  have small : 4<(types G).card := by
    by_contra! low
    exact (Nat.not_le_of_gt bad) (exact_of_at_most_four G conn ord low)
  have need := six_required G bad (C:=rich G) ⟨Subset.rfl,fun _ _ _ m _ => m⟩ (by omega)
  omega

/-- Two distinct internal levels in one nontrivial component suffice even
when their numerical values are arbitrarily far apart. -/
theorem exact_of_two_component_types {C : Finset V} (comp : Closed G C) (nontrivial : 2≤C.card)
    (few : (C.image (EarTriangleLoss.inside G)).card≤2) : gamma G≤bound G := by
  classical
  by_contra! bad
  let P := C.image (EarTriangleLoss.inside G)
  have sub : C⊆CollisionPalette.atLevels G P := fun w wm =>
    mem_filter.mpr ⟨comp.rich wm,mem_image_of_mem _ wm⟩
  have a := (card_le_card sub).trans (CollisionPalette.spectral_bound G bad P)
  have b := (card_filter_le (P∪P.image Nat.succ) (fun n : ℕ => 2 ≤ n)).trans (card_union_le ..)
  have c := card_image_le (s:=P) (f:=Nat.succ)
  have lim := six_required G bad comp nontrivial
  change P.card≤2 at few
  omega

theorem induced_palette : types (G.induce (rich G:Set V))=CollisionPalette.palette G := by
  classical
  ext n; constructor
  · intro m; obtain ⟨v,_,eq⟩ := mem_image.mp m
    exact mem_image.mpr ⟨v.val,v.2,(RichCore.induced_score G v).symm.trans eq⟩
  · intro m; obtain ⟨v,vm,eq⟩ := mem_image.mp m
    exact mem_image.mpr ⟨⟨v,vm⟩,mem_univ _,(RichCore.induced_score G ⟨v,vm⟩).trans eq⟩

theorem exact_of_three_core_types (conn : G.Connected) (ord : 2<Fintype.card V)
    (few : (types (G.induce (rich G:Set V))).card≤3) : gamma G≤bound G := by
  rw [induced_palette] at few
  exact exact_of_three_internal_types G conn ord few

end Graffiti384b.OddStars.RichBlockFinish
#print axioms Graffiti384b.OddStars.RichBlockFinish.universal_of_four
#print axioms Graffiti384b.OddStars.RichBlockFinish.six_required
#print axioms Graffiti384b.OddStars.RichBlockFinish.exact_of_span_two
#print axioms Graffiti384b.OddStars.RichBlockFinish.exact_of_three_internal_types
#print axioms Graffiti384b.OddStars.RichBlockFinish.exact_of_two_component_types
#print axioms Graffiti384b.OddStars.RichBlockFinish.induced_palette
#print axioms Graffiti384b.OddStars.RichBlockFinish.exact_of_three_core_types
