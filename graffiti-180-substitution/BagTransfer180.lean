import BagLeaves180
import BagColor180
import BagSections180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [Fintype V] [DecidableEq B] in
theorem extra_count (s t : B→V) (A P : Finset V) (inside : ∀ i,s i∈A → s i=t i) :
    (A\univ.image t).card+(P\univ.image s).card≤
    ((A∪P)\univ.image s).card+((A∩P)\univ.image t).card := by
  classical
  let X := A\univ.image t
  let Y := P\univ.image s
  have no {x : V} (xx : x∈X) : x∉univ.image s := by
    intro hit
    obtain ⟨i,_,rfl⟩ := mem_image.mp hit
    exact (mem_sdiff.mp xx).2 (inside i (mem_sdiff.mp xx).1 ▸ mem_image_of_mem _ (mem_univ _))
  have u : X∪Y⊆(A∪P)\univ.image s := by
    intro x xm
    rcases mem_union.mp xm with xa|xp
    · exact mem_sdiff.mpr ⟨mem_union_left _ (mem_sdiff.mp xa).1,no xa⟩
    · exact mem_sdiff.mpr ⟨mem_union_right _ (mem_sdiff.mp xp).1,(mem_sdiff.mp xp).2⟩
  have v : X∩Y⊆(A∩P)\univ.image t := by
    intro x xm
    obtain ⟨a,b⟩ := mem_inter.mp xm
    exact mem_sdiff.mpr ⟨mem_inter.mpr ⟨(mem_sdiff.mp a).1,(mem_sdiff.mp b).1⟩,(mem_sdiff.mp a).2⟩
  have eq := card_union_add_card_inter X Y
  have := card_le_card u
  have := card_le_card v
  change X.card+Y.card≤_
  omega

/-- Transfer a single root and parity from the base. A common maximum
bipartite witness is needed only on each independent support separately. -/
theorem Bags.localLift (h : Bags H G f) (cover : CoversBags H G f) (gc : G.Connected)
    (hn : 2<Fintype.card B) (nohub : ∀ i,¬Universal G i) (r : V) (p : Bool)
    (base : localBound G (f r) (parity G (f r) p)) : localBound H r (parity H r p) := by
  classical
  intro A ai
  let P := parity H r p
  let Q := parity G (f r) p
  let U := eligible A P r
  obtain ⟨s,t,ss,st,root,off,even,inside,avoid⟩ := h.sections r p A ai
  have reserve := h.reserve cover A P ai t st avoid
  have lf := h.liftLeaves gc hn nohub s ss U
  obtain ⟨ue,pe⟩ := h.eligible_pull gc r p A s t ss root off even
  have ind : Indep G (pull t A) := fun i mi j mj ne e =>
    ai _ (mem_pull.mp mi) _ (mem_pull.mp mj) (fun eq => ne (st.injective eq)) ((h.repHom t st).map_adj e)
  have old := base _ ind
  change 1+(pull t A).card+Q.card≤weightedLeaves G (eligible (pull t A) Q (f r))+bipartiteNum G at old
  change pull s U=eligible (pull t A) Q (f r) at ue
  rw [ue] at lf
  have ac := section_count t st.injective A
  have pc := section_count s ss.injective P
  change pull s P=Q at pe
  rw [pe] at pc
  have eq : U\univ.image s=(A∪P)\univ.image s := by
    ext x
    have rin : r∈univ.image s := root ▸ mem_image_of_mem s (mem_univ (f r))
    simp only [U,mem_sdiff,eligible_iff,mem_union]
    by_cases same : x=r
    · subst x; simp [rin]
    · simp [same]
  rw [eq] at lf
  have extras := extra_count s t A P inside
  change 1+A.card+P.card≤weightedLeaves H U+bipartiteNum H
  omega

#print axioms extra_count
#print axioms Bags.localLift
end Minimal180.Substitution
