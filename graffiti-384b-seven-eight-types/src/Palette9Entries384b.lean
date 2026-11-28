import Palette9Normalize384b
import Palette9Tree384b
import Palette9Score384b

namespace Graffiti384b.SmallPalette.N9
open Graffiti384b.SmallPalette
open Finset SimpleGraph
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000

private def pairsSix : Fin 21→Label×Label :=
  ![(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,4),(3,5),(3,6),(3,7),(3,8),(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)]

private theorem slot_total : ∀ i j : Label, 2≤i.val→i<j→
    ∃ k : Fin 21,k.val=slot 9 i.val j.val ∧ pairsSix k=(i,j) := by decide

private theorem data_eq : ∀ s : Fin 28,
    let S := forms9 s
    let T := GraffitiSmallNorm9.anchorTable s
    (S.edge01=true↔T.1=1) ∧ (if S.edge01 then 1 else 0)=T.1 ∧
      S.d0=T.2.1 ∧ S.d1=T.2.2.1 ∧ S.common=T.2.2.2 := by decide

private theorem degree_triangle_bound {W : Type*} [Fintype W] [DecidableEq W] (J : SimpleGraph W)
    [DecidableRel J.Adj] (v : W) : trianglesAt J v≤(J.degree v).choose 2 := by
  unfold trianglesAt
  exact (card_filter_le _ _).trans_eq (by rw [card_powersetCard,card_neighborFinset_eq_degree])

variable (G : SimpleGraph Label) [DecidableRel G.Adj]

/-- The actual graph supplies the free bits; all anchor rows remain fixed. -/
theorem entries_of_shape (s : Fin 28) (p : Label≃Label)
    (edge01 : G.Adj (p 0) (p 1)↔(GraffitiSmallNorm9.anchorTable s).1=1)
    (contact : ∀ j : Label,2≤j.val→
      let t := GraffitiSmallNorm9.anchorTable s
      let a := t.2.1-t.1
      let b := t.2.2.1-t.1
      let c := t.2.2.2
      let r := j.val-2
      (G.Adj (p 0) (p j)↔r<a) ∧
      (G.Adj (p 1) (p j)↔r<c ∨ (a≤r ∧ r<a+b-c))) :
    ∃ bits : Nat→Bool, ∀ i j,adj (forms9 s) bits i j=true↔G.Adj (p i) (p j) := by
  let bits (k : Nat) := if h:k<21 then
    let t := pairsSix ⟨k,h⟩
    decide (G.Adj (p t.1) (p t.2))
    else false
  refine ⟨bits,?_⟩
  have ordered (i j : Label) (lt : i<j) : adj (forms9 s) bits i j=true↔G.Adj (p i) (p j) := by
    have ni : i.val < j.val := lt
    dsimp [adj]
    simp only [min_eq_left ni.le,max_eq_right ni.le,if_neg (ne_of_lt ni)]
    have eq := data_eq s
    by_cases z : i.val=0
    · have zi : i=0 := Fin.ext z
      rw [if_pos z]
      by_cases w : j.val=1
      · have wj : j=1 := Fin.ext w
        simpa only [if_pos w,zi,wj] using eq.1.trans edge01.symm
      have up : 2≤j.val := by omega
      rw [if_neg w,zi]
      simpa only [anchorZero,eq.2.1,eq.2.2.1,decide_eq_true_eq] using (contact j up).1.symm
    rw [if_neg z]
    by_cases o : i.val=1
    · have oi : i=1 := Fin.ext o
      have up : 2≤j.val := by omega
      rw [if_pos o,oi]
      simpa only [anchorOne,eq.2.1,eq.2.2.1,eq.2.2.2.1,eq.2.2.2.2,decide_eq_true_eq]
        using (contact j up).2.symm
    rw [if_neg o]
    obtain ⟨k,kVal,matchPair⟩ := slot_total i j (by omega) lt
    rw [←kVal]
    simp only [bits,dif_pos k.isLt,matchPair,decide_eq_true_eq]
  intro i j
  rcases lt_trichotomy i j with lo|same|hi
  · exact ordered i j lo
  · subst j
    simp [adj,G.loopless]
  · have swap : adj (forms9 s) bits i j = adj (forms9 s) bits j i := by simp [adj,min_comm,max_comm]
    rw [swap,SimpleGraph.adj_comm]
    exact ordered j i hi


#print axioms entries_of_shape
end Graffiti384b.SmallPalette.N9
