import ThirtyPairSaving31

namespace Graffiti384b.ThirtyCore
open Finset SimpleGraph
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private Prune.outside_zero from Prune384b
open private Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The cubic pair in the thirty-vertex positive core has at most one
common neighbor. At least three vertices of every five-clique see the
pair, and every five-clique meets the score-three cubic's neighborhood. -/
theorem pair_profile (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
    ∃ u s : P,H.degree u=3 ∧ trianglesAt H u=2 ∧ u∉R ∧ H.degree s=3 ∧ trianglesAt H s=3 ∧ s∉R ∧
      ¬H.Adj u s ∧ (H.neighborFinset u∩H.neighborFinset s).card≤1 ∧
      ∀ C,H.IsNClique 5 C → 3≤(C∩(H.neighborFinset u∪H.neighborFinset s)).card ∧ ∃ x∈C,H.Adj s x := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
  obtain ⟨⟨C,cl⟩,⟨e,de⟩,_,v,_,_,vs,meet⟩ := failure G conn t q bad
  obtain ⟨size,_,_,fi,pos,g⟩ := Frontier31.positive_core G conn t q bad
  obtain ⟨a,b,ea,eb,ab⟩ := (TrianglePrune.triangle_iff H e).mp (pos e)
  have half : Fintype.card P≤2*gamma H := by rw [size,show gamma H=15 from g]
  have tight : CliquePivot33.Tight H R := Frontier31.rooted_tight G t q bad
  obtain ⟨u,s,du,su,ur,ds,ss,sr⟩ := both_required H de ea eb ab pos fi cl half tight
  have few : (H.neighborFinset u∩H.neighborFinset s).card≤1 := by
    apply card_le_one.mpr
    intro p pm z zm
    by_contra ne
    obtain ⟨up,sp⟩ := mem_inter.mp pm
    obtain ⟨uz,sz⟩ := mem_inter.mp zm
    have hit (K : Finset P) (kc : H.IsNClique 5 K) : p∈K ∨ z∈K := ForcedCubics.shared_transversal H de ea eb ab pos fi du su ds ss ne
      ((H.mem_neighborFinset ..).mp up) ((H.mem_neighborFinset ..).mp uz)
      ((H.mem_neighborFinset ..).mp sp) ((H.mem_neighborFinset ..).mp sz) tight kc
    have small := shared_saving H size du su ds ss ne ((H.mem_neighborFinset ..).mp up)
      ((H.mem_neighborFinset ..).mp uz) ((H.mem_neighborFinset ..).mp sp) ((H.mem_neighborFinset ..).mp sz)
      pos fi hit
    change gamma H=15 at g; omega
  have nonadj : ¬H.Adj u s := by
    intro ed
    have sub : (H.neighborFinset s).erase u⊆H.neighborFinset u∩H.neighborFinset s := by
      intro w wm
      obtain ⟨wu,ws⟩ := mem_erase.mp wm
      exact mem_inter.mpr ⟨(H.mem_neighborFinset ..).mpr (EarAnchor.full_neighbors H ds ss
        ed.symm ((H.mem_neighborFinset ..).mp ws) wu.symm),ws⟩
    have h := (card_le_card sub).trans few
    rw [card_erase_of_mem ((H.mem_neighborFinset ..).mpr ed.symm),card_neighborFinset_eq_degree,ds] at h
    omega
  refine ⟨u,s,du,su,ur,ds,ss,sr,nonadj,few,?_⟩
  intro K kc
  have miss := ForcedCubics.clique_remainder H du su ds ss pos fi tight kc
  have total := (card_sdiff_add_card_inter K (H.neighborFinset u∪H.neighborFinset s)).trans kc.2
  have many : 3≤(K∩(H.neighborFinset u∪H.neighborFinset s)).card := by omega
  exact ⟨many,fi (vs.trans ss.symm) ▸ meet K kc⟩

/-- At the original nonleaf quota, any failure has two distinct cubic
vertices of scores two and three, separated from every vertex below
degree two. In particular the criterion holds at every graph order. -/
theorem original_pair (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    (bad : bound G<gamma G) :
    ∃ u s,G.degree u=3 ∧ trianglesAt G u=2 ∧ G.degree s=3 ∧ trianglesAt G s=3 ∧ ¬G.Adj u s ∧
      G.neighborFinset u⊆nonleaves G ∧ G.neighborFinset s⊆nonleaves G ∧
      (G.neighborFinset u∩G.neighborFinset s).card≤1 := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
  obtain ⟨u,s,du,su,ur,ds,ss,sr,us,few,_⟩ := pair_profile G conn t q bad
  have support (w : P) (off : w∉R) : G.neighborFinset w.val⊆P := by
    intro z zm; by_contra away
    exact off (mem_filter.mpr ⟨mem_univ _,z,away,(G.mem_neighborFinset ..).mp zm⟩)
  have degree (w : P) (off : w∉R) : H.degree w=G.degree w.val := by
    rw [EarAnchor.induced_degree]
    have eq : P.filter (G.Adj w.val)=G.neighborFinset w.val := by
      ext z; simp only [mem_filter,G.mem_neighborFinset]
      exact ⟨And.right,fun adj => ⟨support w off ((G.mem_neighborFinset ..).mpr adj),adj⟩⟩
    exact (congrArg card eq).trans (card_neighborFinset_eq_degree ..)
  have sc (w : P) : trianglesAt H w=trianglesAt G w.val := Prune.counts_preserved G P Subset.rfl w
  refine ⟨u.val,s.val,(degree u ur).symm.trans du,(sc u).symm.trans su,
    (degree s sr).symm.trans ds,(sc s).symm.trans ss,us,support u ur,support s sr,?_⟩
  apply card_le_one.mpr
  intro p pm z zm
  obtain ⟨up,sp⟩ := mem_inter.mp pm
  obtain ⟨uz,sz⟩ := mem_inter.mp zm
  let a : P := ⟨p,support u ur up⟩
  let b : P := ⟨z,support u ur uz⟩
  have eq : a=b := card_le_one.mp few a (mem_inter.mpr
    ⟨(H.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp up),(H.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp sp)⟩) b
    (mem_inter.mpr ⟨(H.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp uz),(H.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp sz)⟩)
  exact congrArg Subtype.val eq

/-- Removing all but one of the vertices below degree two preserves the
nonleaf quota as well as the palette of the induced order-31 failure. -/
theorem induced31 (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    (bad : bound G<gamma G) :
    ∃ S : Finset V,S.card=31 ∧ (G.induce (S:Set V)).Connected ∧
      types (G.induce (S:Set V))=types G ∧ (nonleaves (G.induce (S:Set V))).card=30 ∧
      bound (G.induce (S:Set V))<gamma (G.induce (S:Set V)) := by
  classical
  have total := card_le_univ (nonleaves G)
  obtain ⟨S,keep,max,_,connected,same,fail⟩ := Prune.prune_failure G conn (by omega) bad
  let H := G.induce (S:Set V)
  have tj : (types H).card=31 := (congrArg card same).trans t
  have atmost : (types H).card≤S.card := by
    simpa [types] using (card_image_le (s:=(univ:Finset S)) (f:=trianglesAt H))
  have size : S.card=31 := by omega
  have low := Frontier31.enough H tj
  have sub : (nonleaves H).map (Function.Embedding.subtype _)⊆nonleaves G := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := mem_map.mp vm
    have dh : H.degree w≤G.degree w.val := by
      rw [EarAnchor.induced_degree,←card_neighborFinset_eq_degree G w.val]
      exact card_le_card (fun z m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp wm).2).trans dh⟩
  have upper := card_le_card sub
  rw [card_map,q] at upper
  exact ⟨S,size,connected,same,Nat.le_antisymm upper low,fail⟩

end Graffiti384b.ThirtyCore
#print axioms Graffiti384b.ThirtyCore.pair_profile
#print axioms Graffiti384b.ThirtyCore.original_pair
#print axioms Graffiti384b.ThirtyCore.induced31
