import FrontierTwentyNine384b
import ThirtyBoth31

namespace Graffiti384b.Core28
open Finset SimpleGraph
open private OneEar.trim OneEar.trim_scores OneEar.deg2 from OneEarFinish384b
open private TrianglePrune.Closed TrianglePrune.scores_closed TrianglePrune.induced_cost TrianglePrune.triangle_iff from TrianglePrune384b
open private OddQuota.positive_half from OddQuota384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev shore (S : Finset V) := (OneEar.trim G).induce (S:Set V)

omit [DecidableRel G.Adj] in
theorem closed_compl {S : Finset V} (cl : OddQuota.TriangleClosed G S) :
    OddQuota.TriangleClosed G Sᶜ := by
  intro v vm w z vw vz wz
  exact mem_compl.mpr (fun wm => mem_compl.mp vm (cl w wm v z vw.symm wz vz))

/-- Each triangle-closed side inherits every vertex score and is itself half-tight. -/
theorem shore_data (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (tight : Fintype.card V≤2*gamma G) (S : Finset V) (closed : OddQuota.TriangleClosed G S) :
    (∀ v:S,trianglesAt (shore G S) v=trianglesAt G v.val) ∧ 2*gamma (shore G S)=S.card := by
  classical
  let J := OneEar.trim G
  have cj : TrianglePrune.Closed J S := by
    intro v vm w vw
    rcases vw.2 with ⟨z,vz,wz⟩|vz|wz
    · exact closed v vm w z vw.1 vz wz
    · exact (Nat.ne_of_gt (pos v) vz).elim
    · exact (Nat.ne_of_gt (pos w) wz).elim
  have ct : TrianglePrune.Closed J Sᶜ := fun v vm w vw => mem_compl.mpr
    (fun ws => mem_compl.mp vm (cj w ws v vw.symm))
  have sides {U : Finset V} (cu : TrianglePrune.Closed J U) :
      2*gamma (J.induce (U:Set V))≤U.card := by
    let K := J.induce (U:Set V)
    have score (v : U) : trianglesAt K v=trianglesAt G v.val :=
      (TrianglePrune.scores_closed J U cu v).trans (OneEar.trim_scores G v.val)
    have p (v : U) : 0<trianglesAt K v := (score v) ▸ pos v.val
    have i : Function.Injective (trianglesAt K) := fun v w h => Subtype.ext
      (fi ((score v).symm.trans (h.trans (score w))))
    exact (OddQuota.positive_half K p i).trans_eq (Fintype.card_coe U)
  have a := sides cj
  have b := sides ct
  have ca := TrianglePrune.induced_cost J S
  have cb := TrianglePrune.induced_cost J Sᶜ
  have split := Capacity.separated_add J S Sᶜ ∅ disjoint_compl_right
    (fun v vm w wm vw => mem_compl.mp wm (cj v vm w vw))
  rw [union_compl] at split
  have upper := Capacity.seeded_value J ∅ univ ∅ (by simp) (by simp) (by simp) (by simp)
  simp only [card_empty,zero_add] at upper
  have mono : gamma G≤gamma J := by
    have existsD : {k : ℕ | ∃ D,TwoDominates J D ∧ D.card=k}.Nonempty :=
      ⟨_,univ,by simp [TwoDominates],rfl⟩
    obtain ⟨D,dom,sz⟩ := Nat.sInf_mem existsD
    exact Nat.sInf_le ⟨D,fun v out => (dom v out).trans (card_le_card
      (show D.filter (J.Adj v)⊆D.filter (G.Adj v) from fun _ m =>
        mem_filter.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.1⟩)),sz⟩
  have size := card_le_univ S
  have part := card_compl S
  refine ⟨fun v => (TrianglePrune.scores_closed J S cj v).trans (OneEar.trim_scores G v.val),?_⟩
  change 2*gamma (J.induce (S:Set V))=S.card
  omega

theorem clique_scores (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (half : Fintype.card V≤2*gamma G) {C : Finset V} (cl : G.IsNClique 5 C) :
    Icc 1 3⊆types G := by
  classical
  have tight : CliquePivot33.Tight G ∅ := by
    intro D rel
    have dom : TwoDominates G D := fun v out => by simpa using rel v out
    have up : gamma G≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    omega
  have two (v : V) : 2≤G.degree v := by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff G v).mp (pos v)
    exact OneEar.deg2 G ab.ne va vb
  by_cases ear : ∃ e,G.degree e=2
  · obtain ⟨e,de⟩ := ear
    obtain ⟨a,b,ea,eb,ab⟩ := (TrianglePrune.triangle_iff G e).mp (pos e)
    obtain ⟨u,v,_,su,_,_,sv,_⟩ := ThirtyCore.both_required G de ea eb ab pos fi cl half tight
    have cap := Repair.triangles_le_choose G e
    rw [de,Nat.choose_self] at cap
    have se : trianglesAt G e=1 := by have := pos e; omega
    intro i im
    have := mem_Icc.mp im
    rcases (show i=1 ∨ i=2 ∨ i=3 by omega) with rfl|rfl|rfl
    · exact mem_image.mpr ⟨e,mem_univ _,se⟩
    · exact mem_image.mpr ⟨u,mem_univ _,su⟩
    · exact mem_image.mpr ⟨v,mem_univ _,sv⟩
  · have minD (v : V) : 2≤G.degree v ∧ (v∉(∅:Finset V) → 3≤G.degree v) :=
      ⟨two v,fun _ => by have := two v; have ne : G.degree v≠2 := fun eq => ear ⟨v,eq⟩; omega⟩
    have h := (CliquePivot33.three_cubics G ∅ minD pos fi tight cl).2.1
    rw [←h]
    exact image_subset_image (subset_univ _)

end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.shore_data
#print axioms Graffiti384b.Core28.clique_scores
