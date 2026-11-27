import HighFrontier28
import PortSaving28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph HighEar Core28 Four28
open private Four28.core_data from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem adjacent_common {u v : V} (dv : H.degree v=3) (sv : trianglesAt H v=3)
    (uv : H.Adj u v) : 2≤(H.neighborFinset u∩H.neighborFinset v).card := by
  have sub : (H.neighborFinset v).erase u⊆H.neighborFinset u∩H.neighborFinset v := by
    intro w wm
    obtain ⟨wu,ww⟩ := mem_erase.mp wm
    exact mem_inter.mpr ⟨(H.mem_neighborFinset ..).mpr
      (EarAnchor.full_neighbors H dv sv uv.symm ((H.mem_neighborFinset ..).mp ww) wu.symm),ww⟩
  have bound := card_le_card sub
  rwa [card_erase_of_mem ((H.mem_neighborFinset ..).mpr uv.symm),card_neighborFinset_eq_degree,dv] at bound

theorem common_saving {u v : V} (n : Fintype.card V=28) (pos : ∀ w,0<trianglesAt H w)
    (fi : Function.Injective (trianglesAt H)) (free : H.CliqueFree 5)
    (du : H.degree u=3) (su : trianglesAt H u=2) (dv : H.degree v=3) (sv : trianglesAt H v=3)
    (ne : (H.neighborFinset u∩H.neighborFinset v).Nonempty) : gamma H≤13 := by
  by_cases many : 1<(H.neighborFinset u∩H.neighborFinset v).card
  · obtain ⟨p,pm,q,qm,pq⟩ := one_lt_card.mp many
    obtain ⟨up,vp⟩ := mem_inter.mp pm
    obtain ⟨uq,vq⟩ := mem_inter.mp qm
    exact CorePair28.shared_saving H n du su dv sv pq
      ((H.mem_neighborFinset ..).mp up) ((H.mem_neighborFinset ..).mp uq)
      ((H.mem_neighborFinset ..).mp vp) ((H.mem_neighborFinset ..).mp vq) pos fi
      (fun C cl => (free C cl).elim)
  · have hpos := card_pos.mpr ne
    obtain ⟨c,hc⟩ := card_eq_one.mp (by omega : (H.neighborFinset u∩H.neighborFinset v).card=1)
    have sep : ¬H.Adj u v := fun h => many (adjacent_common H dv sv h)
    exact (⟨u,v,c,du,su,dv,sv,sep,hc⟩ : Port28.Board H).saving n pos fi free

/-- The two external cubics forced by the ear and the five-vertex fan have
disjoint neighbor triples and do not touch. Every fourth vertex has
degree at least five and lies in at least four triangles. -/
theorem disjoint_frontier (t : (types H).card=29) (q : (nonleaves H).card=28) (bad : bound H<gamma H) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b,J.Adj a b → J.neighborFinset e={a,b} →
      (additional J e a b).Nonempty ∧ 4≤J.degree a ∧ 4≤J.degree b ∧
      (∀ s∈additional J e a b,5≤J.degree s ∧ 4≤trianglesAt J s) ∧
      ∃ T Y,Fan J T Y ∧ Disjoint (T∪Y) {e,a,b} ∧ ∃ u v,
        u∉T∪Y∪{e,a,b} ∧ v∉T∪Y∪{e,a,b} ∧ J.degree u=3 ∧ J.degree v=3 ∧
        trianglesAt J u=2 ∧ trianglesAt J v=3 ∧ ¬J.Adj u v ∧
        Disjoint (J.neighborFinset u) (J.neighborFinset v) := by
  classical
  dsimp only
  intro free e a b ab en
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data H t q bad
  obtain ⟨add,da,db,hard,T,Y,fan,off,u,v,um,vm,du,dv,su,sv⟩ :=
    forced_pair H t q bad free e a b ab en
  have small : ¬(J.neighborFinset u∩J.neighborFinset v).Nonempty := by
    intro common
    exact (Nat.not_succ_le_self 13) (half.trans (common_saving J n pos fi free du su dv sv common))
  have dis : Disjoint (J.neighborFinset u) (J.neighborFinset v) :=
    disjoint_left.mpr (by intro w a b; exact small ⟨w,mem_inter.mpr ⟨a,b⟩⟩)
  have no : ¬J.Adj u v := by
    intro h
    have z := adjacent_common J dv sv h
    rw [disjoint_iff_inter_eq_empty.mp dis,card_empty] at z
    omega
  exact ⟨add,da,db,hard,T,Y,fan,off,u,v,um,vm,du,dv,su,sv,no,dis⟩

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.common_saving
#print axioms Graffiti384b.HighSquare28.disjoint_frontier
