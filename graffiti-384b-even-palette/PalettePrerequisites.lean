import OneEarRoute384b
import OneEarCut384b
import TrianglePrune384b

namespace Graffiti384b.PositivePalette.Prerequisites
open Finset SimpleGraph OneEar
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

-- These four lemmas are extracted from the frozen files listed in SOURCE-MAP.tsv.

theorem deg2 {v x y : V} (xy : x≠y) (vx : G.Adj v x) (vy : G.Adj v y) : 2≤G.degree v := by
  have sub := insert_subset ((G.mem_neighborFinset _ _).mpr vx)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr vy))
  have h := card_le_card sub
  rwa [card_pair xy,card_neighborFinset_eq_degree] at h

theorem route_of_reach {e a b : V} (ear : G.neighborFinset e={a,b}) (eb : G.Adj e b) (ab : G.Adj a b)
    (reach : (opened G {e,a,b}).Reachable a b) : ∃ n, 2≤n ∧ Nonempty (Route G e a b n) := by
  classical
  let K : Finset V := {e,a,b}
  let H := opened G K
  obtain ⟨p,hp⟩ := reach.exists_isPath
  let f := p.getVert
  have one : 1≤p.length := by
    by_contra! short
    have zero : p.length=0 := by omega
    exact ab.ne (p.getVert_zero.symm.trans (zero ▸ p.getVert_length))
  have two : 2≤p.length := by
    by_contra! short
    have l : p.length=1 := by omega
    have edge := p.adj_getVert_succ (i:=0) (by omega)
    rw [p.getVert_zero,show 0+1=p.length by omega,p.getVert_length] at edge
    exact edge.2 ⟨by simp [K],by simp [K]⟩
  have st (i : ℕ) (hi : i < p.length) : H.Adj (f i) (f (i+1)) := p.adj_getVert_succ hi
  have iso {v : V} (edge : H.Adj e v) : False := by
    have vm := (G.mem_neighborFinset _ _).mpr edge.1
    rw [ear] at vm
    exact edge.2 ⟨by simp [K],mem_insert_of_mem vm⟩
  let r : Route G e a b p.length := {
    atIdx := f
    start := p.getVert_zero
    finish := p.getVert_length
    step := fun i hi => (st i hi).1
    unique := fun i hi j hj eq => hp.getVert_injOn hi hj eq
    avoid := by
      intro i hi eq
      by_cases lt : i < p.length
      · exact iso (eq ▸ st i lt)
      · have endv : f i=b := (show i=p.length by omega) ▸ p.getVert_length
        exact eb.ne (eq.symm.trans endv)
  }
  exact ⟨p.length,two,⟨r⟩⟩

theorem ear_pair {y : V} (d : G.degree y=2) (p : 0<trianglesAt G y) :
    ∃ a b,G.neighborFinset y={a,b} ∧ G.Adj y a ∧ G.Adj y b ∧ G.Adj a b := by
  obtain ⟨a,b,ya,yb,ab⟩ := (TrianglePrune.triangle_iff G y).mp p
  have sub := insert_subset ((G.mem_neighborFinset _ _).mpr ya) (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr yb))
  exact ⟨a,b,(eq_of_subset_of_card_le sub (by rw [card_pair ab.ne,card_neighborFinset_eq_degree,d])).symm,ya,yb,ab⟩

omit [DecidableEq V] in
theorem gamma_mono (H : SimpleGraph V) [DecidableRel H.Adj] (le : H≤G) : gamma G≤gamma H := by
  have avail : {k : ℕ | ∃ D, TwoDominates H D ∧ D.card=k}.Nonempty := ⟨_,univ,by simp [TwoDominates],rfl⟩
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem avail
  exact Nat.sInf_le ⟨D,fun v out => (dom v out).trans (card_le_card
    (show D.filter (H.Adj v)⊆D.filter (G.Adj v) from fun w wm => mem_filter.mpr ⟨(mem_filter.mp wm).1,le (mem_filter.mp wm).2⟩)),sz⟩

end Graffiti384b.PositivePalette.Prerequisites
#print axioms Graffiti384b.PositivePalette.Prerequisites.route_of_reach
