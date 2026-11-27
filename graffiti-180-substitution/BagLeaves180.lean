import BagMetric180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [Fintype V] [DecidableEq B] in
theorem section_count (s : B→V) (inj : Function.Injective s) (S : Finset V) :
    S.card=(pull s S).card+(S\univ.image s).card := by
  classical
  have eq : (pull s S).image s=S∩univ.image s := by
    ext v
    constructor
    · rintro h; obtain ⟨i,m,rfl⟩ := mem_image.mp h
      exact mem_inter.mpr ⟨mem_pull.mp m,mem_image_of_mem _ (mem_univ _)⟩
    · intro h; obtain ⟨i,_,rfl⟩ := mem_image.mp (mem_inter.mp h).2
      exact mem_image.mpr ⟨i,mem_pull.mpr (mem_inter.mp h).1,rfl⟩
  have part := card_sdiff_add_card_inter S (univ.image s)
  rw [←eq,card_image_of_injective _ inj] at part; omega

omit [Fintype V] [Fintype B] in
theorem Bags.coreLift (h : Bags H G f) (s : B→V) (sec : Function.LeftInverse f s) (D : Finset B)
    (big : 1<D.card) (con : Con G D) (dom : ∀ i∉D,Dominates G D i) :
    Con H (D.image s) ∧ ∀ x∉D.image s,Dominates H (D.image s) x := by
  classical
  let em : G.induce (D : Set B) →g H.induce (D.image s : Set V) :=
    ⟨fun i => ⟨s i.val,mem_image_of_mem _ i.property⟩,fun {a b} e => (h.repHom s sec).map_adj e⟩
  constructor
  · obtain ⟨i⟩ := con.nonempty
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨em i,fun y => ?_⟩
    obtain ⟨j,jd,same⟩ := mem_image.mp y.property
    have eq : em ⟨j,jd⟩=y := Subtype.ext same
    exact eq ▸ (con i ⟨j,jd⟩).map em
  · intro x _
    have neighbor : ∃ j∈D,G.Adj (f x) j := by
      by_cases xd : f x∈D
      · have size : 1<Fintype.card ↥D := by simpa only [Fintype.card_coe] using big
        obtain ⟨j,e⟩ := exists_adj _ con size ⟨f x,xd⟩
        exact ⟨j.val,j.property,e⟩
      · exact dom (f x) xd
    obtain ⟨j,jd,e⟩ := neighbor
    exact ⟨s j,mem_image_of_mem _ jd,h.edgeUp (by rwa [sec j])⟩

/-- All eligible vertices outside the representative set can be added to
the lower leaf score, even with arbitrary edges inside individual bags.
A base with no universal vertex has no singleton connected dominating core. -/
theorem Bags.liftLeaves (h : Bags H G f) (gc : G.Connected) (hn : 2<Fintype.card B)
    (nohub : ∀ i,¬Universal G i) (s : B→V) (sec : Function.LeftInverse f s) (U : Finset V) :
    weightedLeaves G (pull s U)+(U\univ.image s).card≤weightedLeaves H U := by
  classical
  obtain ⟨T,sub,tr,opt⟩ := tree_opt G gc (pull s U)
  let L := pull s U∩leaves T
  let D := univ\L
  have ⟨con,domin⟩ := leaf_core G T sub tr hn L inter_subset_right
  have dom (x : B) (m : x∉D) : Dominates G D x := domin _ (by simpa [D] using m)
  have big : 1<D.card := by
    obtain ⟨i⟩ := con.nonempty
    have pos : D.Nonempty := ⟨i.val,i.property⟩
    by_contra! small
    obtain ⟨j,sing⟩ := card_eq_one.mp (le_antisymm small (card_pos.mpr pos))
    apply nohub j
    intro v ne
    obtain ⟨w,wm,e⟩ := dom v (by simpa [sing] using ne)
    rw [sing,mem_singleton] at wm; exact wm ▸ e
  have ⟨up,cover⟩ := h.coreLift s sec D big con dom
  have bound := weightedCore H (D.image s) U up cover
  have inc : L.image s ∪ (U\univ.image s) ⊆ U\D.image s := by
    intro x hx
    rcases mem_union.mp hx with hl|outside
    · obtain ⟨i,im,rfl⟩ := mem_image.mp hl
      refine mem_sdiff.mpr ⟨mem_pull.mp (mem_inter.mp im).1,?_⟩
      intro hit; obtain ⟨j,jd,same⟩ := mem_image.mp hit
      exact (mem_sdiff.mp jd).2 (sec.injective same ▸ im)
    · exact mem_sdiff.mpr ⟨(mem_sdiff.mp outside).1,fun hit =>
        (mem_sdiff.mp outside).2 ((image_subset_image (subset_univ D)) hit)⟩
  have dis : Disjoint (L.image s) (U\univ.image s) := disjoint_left.mpr (fun x hx h2 =>
    (mem_sdiff.mp h2).2 ((image_subset_image (subset_univ L)) hx))
  have c := card_le_card inc
  rw [card_union_of_disjoint dis,card_image_of_injective _ sec.injective] at c
  change L.card=weightedLeaves G (pull s U) at opt
  omega

#print axioms section_count
#print axioms Bags.coreLift
#print axioms Bags.liftLeaves
end Minimal180.Substitution
