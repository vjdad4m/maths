import OddQuota384b

namespace Graffiti384b.OddQuota
open Finset SimpleGraph
open private OneEar.trim OneEar.trim_scores from OneEarFinish384b
open private TrianglePrune.Closed TrianglePrune.scores_closed TrianglePrune.induced_cost from TrianglePrune384b
open private OddQuota.positive_half from OddQuota384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- No triangle has vertices on both sides of this set. Edges outside
triangles can cross it freely. -/
def TriangleClosed (S : Finset V) : Prop :=
  ∀ v∈S,∀ w z,G.Adj v w → G.Adj v z → G.Adj w z → w∈S

/-- Every union of components formed by triangle edges has even size
in a positive, distinct-count graph attaining the half-order bound. -/
theorem even_shore (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (tight : Fintype.card V≤2*gamma G) (S : Finset V) (closed : TriangleClosed G S) :
    S.card%2=0 := by
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
  omega

/-- An odd triangle-closed shore of the positive nonleaf core supplies
the missing omission at every odd diversity with fewer nonleaves than types. -/
theorem exact_of_odd_shore (odd : (types G).card%2=1) (few : (nonleaves G).card<(types G).card)
    (S : Finset (nonleaves G)) (cl : TriangleClosed (G.induce (nonleaves G:Set V)) S)
    (size : S.card%2=1) : gamma G≤bound G := by
  by_contra! fail
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨pos,fi,tight⟩ := core_of_failure G odd few fail
  have e := even_shore H pos fi ((Fintype.card_coe P).le.trans tight.ge) S cl
  omega

end Graffiti384b.OddQuota
#print axioms Graffiti384b.OddQuota.even_shore
#print axioms Graffiti384b.OddQuota.exact_of_odd_shore
