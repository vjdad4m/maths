import FrontierProfile31

namespace Graffiti384b.Frontier31
open Finset SimpleGraph
open private TrianglePrune.triangle_iff TrianglePrune.induced_cost from TrianglePrune384b
open private Repair.triangles_le_choose from Repair384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the minimum nonleaf quota the positive extremal core exists in all
graphs, including those containing five-cliques. -/
theorem positive_core (hc : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    Fintype.card P=30 ∧ H.Connected ∧ (∀ v : P,trianglesAt H v=trianglesAt G v.val) ∧
      Function.Injective (trianglesAt H) ∧ (∀ v,0<trianglesAt H v) ∧ gamma H=15 := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨same,positive⟩ := positive_types G t q
  have sz : Fintype.card P=30 := (Fintype.card_coe P).trans q
  have conn := Prune.connected_core G hc (Subset.rfl : nonleaves G⊆P) (card_pos.mp (by omega))
  have sc (v : P) : trianglesAt H v=trianglesAt G v.val := Prune.counts_preserved G P Subset.rfl v
  have pos (v : P) : 0<trianglesAt H v := (sc v) ▸ positive v.val v.property
  have fi : Function.Injective (trianglesAt H) := fun v w eq => Subtype.ext (same v.property w.property
    ((sc v).symm.trans (eq.trans (sc w))))
  have allNon : nonleaves H=univ := eq_univ_of_forall (fun v => by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 H ab.ne va vb⟩)
  have highBound := OneEar.unique_one H (by rw [allNon]; exact card_image_le) (fun v _ => pos v)
    (fun v w _ _ a b => fi (a.trans b.symm)) (fun v w a b => fi (a.trans b.symm))
  have typesH : (types H).card=30 := by
    change (univ.image (trianglesAt H)).card=_
    rw [card_image_of_injective _ fi,card_univ]; exact sz
  have up := Capacity.seeded_value G ∅ P ∅ (by simp) (by simp) (by simp) (by simp)
  have cost := TrianglePrune.induced_cost G P
  simp only [card_empty,zero_add] at up
  change P.card≤gamma H + _ at cost
  have pcard : P.card=30 := q
  unfold bound at bad highBound
  change gamma H≤Fintype.card P-((types H).card+1)/2 at highBound
  rw [t] at bad; rw [typesH,sz] at highBound
  have g : gamma H=15 := by omega
  exact ⟨sz,conn,sc,fi,pos,g⟩

/-- Removing all leaves gives the exact positive extremal core. The
score-two cubic and the score-five degree-four vertex retain their degrees. -/
theorem core (hc : G.Connected) (t : (types G).card=31) (cap : ∀ v,G.degree v≤9 → trianglesAt G v≤RankTable.cap (G.degree v) 3)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    Fintype.card P=30 ∧ H.Connected ∧ (∀ v : P,trianglesAt H v=trianglesAt G v.val) ∧
      Function.Injective (trianglesAt H) ∧ (∀ v,0<trianglesAt H v) ∧ gamma H=15 ∧
      (∃ u,H.degree u=3 ∧ trianglesAt H u=2) ∧ ∃ x,H.degree x=4 ∧ trianglesAt H x=5 := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨q,⟨u,du,us⟩,x,dx,xs⟩ := profile G t cap bad
  obtain ⟨sz,conn,sc,fi,pos,g⟩ := positive_core G hc t q bad
  let U : P := ⟨u,mem_filter.mpr ⟨mem_univ _,by omega⟩⟩
  let X : P := ⟨x,mem_filter.mpr ⟨mem_univ _,by omega⟩⟩
  have degree (v : P) : H.degree v≤G.degree v.val := by
    rw [EarAnchor.induced_degree]
    change (P.filter (G.Adj v.val)).card≤G.degree v.val
    rw [←card_neighborFinset_eq_degree]
    exact card_le_card (fun w wm => (G.mem_neighborFinset ..).mpr (mem_filter.mp wm).2)
  have su : trianglesAt H U=2 := (sc U).trans us
  have sx : trianglesAt H X=5 := (sc X).trans xs
  have du' : H.degree U=3 := by
    have h : H.degree U≤3 := (degree U).trans_eq du
    by_contra! different
    have low := (Repair.triangles_le_choose H U).trans (Nat.choose_le_choose 2 (by omega : H.degree U≤2))
    change trianglesAt H U≤1 at low; omega
  have dx' : H.degree X=4 := by
    have h : H.degree X≤4 := (degree X).trans_eq dx
    by_contra! different
    have low := (Repair.triangles_le_choose H X).trans (Nat.choose_le_choose 2 (by omega : H.degree X≤3))
    change trianglesAt H X≤3 at low; omega
  exact ⟨sz,conn,sc,fi,pos,g,⟨U,du',su⟩,X,dx',sx⟩

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.positive_core
#print axioms Graffiti384b.Frontier31.core
