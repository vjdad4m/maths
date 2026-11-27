import FourDiamond28

namespace Graffiti384b.Four28
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle joined to two additional vertices. A five-clique-free graph
has no edge between those two vertices. -/
def Fan (T Y : Finset V) : Prop :=
  G.IsNClique 3 T ∧ Y.card=2 ∧ Disjoint T Y ∧ ∀ t∈T,∀ y∈Y,G.Adj t y

theorem fan_of_book {v : V} (b : book G (G.neighborFinset v)) :
    ∃ T Y,Fan G T Y ∧ v∈T ∧ T∪Y⊆insert v (G.neighborFinset v) := by
  classical
  obtain ⟨C,cn,cl,x,xm,two⟩ := b
  obtain ⟨xn,xc⟩ := mem_sdiff.mp xm
  obtain ⟨D,sub,sz⟩ := exists_subset_card_eq (s:=C.filter (G.Adj x)) two
  have dc : D⊆C := sub.trans (filter_subset ..)
  let T := insert v D
  let Y := insert x (C\D)
  have dcl : G.IsNClique 2 D := ⟨fun a am b bm ne => cl.1 (dc am) (dc bm) ne,sz⟩
  have tcl : G.IsNClique 3 T := dcl.insert (fun a am => (G.mem_neighborFinset ..).mp (cn (dc am)))
  have yc : Y.card=2 := by
    rw [show Y=insert x (C\D) from rfl,card_insert_of_not_mem (fun m => xc (mem_sdiff.mp m).1),
      card_sdiff dc,cl.2,sz]
  have yn : Y⊆G.neighborFinset v := insert_subset xn (sdiff_subset.trans cn)
  have dis : Disjoint T Y := by
    apply disjoint_left.mpr
    intro a am ay
    rcases mem_insert.mp am with rfl|ad
    · exact G.not_mem_neighborFinset_self _ (yn ay)
    · rcases mem_insert.mp ay with rfl|m
      · exact xc (dc ad)
      · exact (mem_sdiff.mp m).2 ad
  have cross : ∀ a∈T,∀ y∈Y,G.Adj a y := by
    intro a am y ym
    rcases mem_insert.mp am with rfl|ad
    · exact (G.mem_neighborFinset ..).mp (yn ym)
    · rcases mem_insert.mp ym with rfl|rem
      · exact (mem_filter.mp (sub ad)).2.symm
      · exact cl.1 (dc ad) (mem_sdiff.mp rem).1 (fun eq => (mem_sdiff.mp rem).2 (eq ▸ ad))
  exact ⟨T,Y,⟨tcl,yc,dis,cross⟩,mem_insert_self ..,union_subset
    (insert_subset_insert _ (dc.trans cn)) (yn.trans (subset_insert ..))⟩

theorem forced_fan (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (free : G.CliqueFree 5) (half : 14≤gamma G)
    (P : Finset V) (size : P.card∈({1,2}:Finset ℕ))
    (special : P.card=2 → ∃ e,trianglesAt G e=1 ∧ 2≤nbr G e P) :
    ∃ v∈remote G P 9,∃ T Y,Fan G T Y ∧ v∈T ∧
      T∪Y⊆insert v (G.neighborFinset v) ∧ Disjoint (T∪Y) P := by
  classical
  obtain ⟨v,vm,b⟩ := remote_book G n pos fi free half P size special
  obtain ⟨T,Y,fan,vt,sub⟩ := fan_of_book G b
  obtain ⟨off,no,_,_⟩ := (mem_filter.mp vm).2
  have noPin : P.filter (G.Adj v)=∅ := card_eq_zero.mp no
  refine ⟨v,vm,T,Y,fan,vt,sub,disjoint_left.mpr ?_⟩
  intro a am ap
  rcases mem_insert.mp (sub am) with rfl|an
  · exact off ap
  · exact (filter_eq_empty_iff.mp noPin ap) ((G.mem_neighborFinset ..).mp an)

omit [Fintype V] [DecidableRel G.Adj] in
theorem tips_unjoined {T Y : Finset V} (fan : Fan G T Y) (free : G.CliqueFree 5)
    {p q : V} (py : p∈Y) (qy : q∈Y) (adj : G.Adj p q) : False := by
  obtain ⟨cl,sz,dis,cross⟩ := fan
  have pc := cl.insert (fun z zm => (cross z zm p py).symm)
  have c : G.IsNClique 5 (insert q (insert p T)) := pc.insert (fun z zm => by
    rcases mem_insert.mp zm with rfl|zt
    · exact adj.symm
    · exact (cross z zt q qy).symm)
  exact free _ c

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.fan_of_book
#print axioms Graffiti384b.Four28.forced_fan
#print axioms Graffiti384b.Four28.tips_unjoined
