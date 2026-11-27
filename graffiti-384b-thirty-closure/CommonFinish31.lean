import CommonSaving31

namespace Graffiti384b.OneCommon
open Finset SimpleGraph
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Any failure with thirty nonleaves has disjoint neighborhoods at the
two required cubics, while retaining the old five-clique coverage. -/
theorem residual (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
    ∃ u s : P,H.degree u=3 ∧ trianglesAt H u=2 ∧ u∉R ∧ H.degree s=3 ∧ trianglesAt H s=3 ∧
      s∉R ∧ ¬H.Adj u s ∧ Disjoint (H.neighborFinset u) (H.neighborFinset s) ∧
      ∀ C,H.IsNClique 5 C → 3≤(C∩(H.neighborFinset u∪H.neighborFinset s)).card ∧ ∃ x∈C,H.Adj s x := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨u,s,du,su,ur,ds,ss,sr,us,few,cover⟩ := ThirtyCore.pair_profile G conn t q bad
  refine ⟨u,s,du,su,ur,ds,ss,sr,us,?_,cover⟩
  apply disjoint_left.mpr
  intro c uc sc
  have cm : c∈H.neighborFinset u∩H.neighborFinset s := mem_inter.mpr ⟨uc,sc⟩
  have common : H.neighborFinset u∩H.neighborFinset s={c} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr cm) (by rw [card_singleton]; exact few)).symm
  let M : Board H := ⟨u,s,c,du,su,ds,ss,us,common⟩
  obtain ⟨n,_,_,fi,pos,gammaH⟩ := Frontier31.positive_core G conn t q bad
  have upper := M.saving n pos fi (fun C cl => (cover C cl).1)
  change gamma H=15 at gammaH
  omega

/-- At any graph order, a common neighbor of the score-two and score-three
cubics suffices for the catalogue inequality in the thirty-nonleaf branch. -/
theorem exact_of_common (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    {u s c : V} (du : G.degree u=3) (su : trianglesAt G u=2)
    (ds : G.degree s=3) (ss : trianglesAt G s=3) (uc : G.Adj u c) (sc : G.Adj s c) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨a,b,_,sa,_,_,sb,_,_,dis,_⟩ := residual G conn t q bad
  have scores (v : P) : trianglesAt H v=trianglesAt G v.val := Prune.counts_preserved G P Subset.rfl v
  have inj := (Frontier31.positive_types G t q).1
  have um : u∈P := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have sm : s∈P := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have au : a.val=u := inj a.property um ((scores a).symm.trans (sa.trans su.symm))
  have bs : b.val=s := inj b.property sm ((scores b).symm.trans (sb.trans ss.symm))
  have us : u≠s := by intro eq; rw [eq,ss] at su; contradiction
  let z : P := ⟨c,mem_filter.mpr ⟨mem_univ _,OneEar.deg2 G us uc.symm sc.symm⟩⟩
  have az : H.Adj a z := (show G.Adj a.val c by rw [au]; exact uc)
  have bz : H.Adj b z := (show G.Adj b.val c by rw [bs]; exact sc)
  exact disjoint_left.mp dis ((H.mem_neighborFinset ..).mpr az) ((H.mem_neighborFinset ..).mpr bz)

end Graffiti384b.OneCommon
#print axioms Graffiti384b.OneCommon.residual
#print axioms Graffiti384b.OneCommon.exact_of_common
