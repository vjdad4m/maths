import CubicCoreStrict33

namespace Graffiti384b.CubicShore
open Finset SimpleGraph EarAnchor EarFrame33 CliquePivot33
open private CubicShore.half_tight CubicShore.square_frame CubicShore.clique_score from CubicDiamondCut33
open private EarAnchor.sees_in_clique from CubicAnchor33
open private Repair.triangles_le_choose from Repair384b

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- If an ear edge lies in another triangle, its third vertex also cannot
realize triangle count two or three in a half-order positive core. -/
theorem third_score {e a c w : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C)
    (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e) : 4≤trianglesAt H w := by
  classical
  apply Nat.le_of_not_gt; intro low
  have one : trianglesAt H e=1 := by
    have cap := Repair.triangles_le_choose H e
    rw [de,Nat.choose_self] at cap; have := pos e; omega
  have wone : trianglesAt H w≠1 := fun h => we (inj (h.trans one.symm))
  have wp := pos w
  have wscore : trianglesAt H w∈Icc 2 3 := mem_Icc.mpr ⟨by omega,by omega⟩
  obtain ⟨C,cl⟩ := five
  let A : Finset V := {e,w}
  let B : Finset V := {a,c}
  have fr : Frame H A B := CubicShore.square_frame H ea ec aw cw we.symm ac.ne
  have tight := CubicShore.half_tight H half
  have covered : 2≤((A∪B)∩C).card := by
    apply Nat.le_of_not_gt; intro small
    obtain ⟨_,_,scores,restr,_⟩ := EarAttachment33.frame_obstruction H de pos inj tight fr
      (show e∈A∪B from mem_union_left _ (mem_insert_self ..)) cl (by omega)
    obtain ⟨t,tm,eq⟩ := mem_image.mp (scores ▸ wscore)
    exact (restr t tm).2.1 (inj eq ▸ mem_union_left _ (mem_insert_of_mem (mem_singleton_self _)))
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have wn : w∉C := fun m => by have := CubicShore.clique_score H cl m; omega
  have sub : ((A∪B)∩C)⊆B := by
    intro x xm; obtain ⟨ab,xc⟩ := mem_inter.mp xm
    rcases mem_union.mp ab with a|b
    · rcases (show x=e ∨ x=w by simpa only [A,mem_insert,mem_singleton] using a) with h|h
      · exact (en (h ▸ xc)).elim
      · exact (wn (h ▸ xc)).elim
    · exact b
  have size : B.card=2 := card_pair ac.ne
  have eq := eq_of_subset_of_card_le sub (by omega)
  have inC : B⊆C := fun x m => (mem_inter.mp (show x∈(A∪B)∩C by rw [eq]; exact m)).2
  have enough (v : V) (va : H.Adj v a) (vc : H.Adj v c) : 2≤nbr H v B :=
    PinnedColor34.two H ac.ne va vc (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
  obtain ⟨_,scores,restrict,_⟩ := EarOnClique33.edge_restriction H de pos inj tight cl inC size (enough e ea ec)
  obtain ⟨t,tm,ts⟩ := mem_image.mp (scores ▸ wscore)
  have lo := enough w aw.symm cw.symm
  have hi := (restrict t tm).2.2.2
  rw [inj ts] at hi
  omega

/-- All three non-ear vertices in the two triangles have at least four
incident triangles. In particular all three have degree at least four. -/
theorem square_profile {e a c w : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C)
    (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e) :
    ∀ t∈({a,c,w} : Finset V),4≤trianglesAt H t ∧ 4≤H.degree t := by
  obtain ⟨sa,sc⟩ := square_scores H de ea ec ac pos inj half five aw cw we
  have sw := third_score H de ea ec ac pos inj half five aw cw we
  intro t tm
  have score : 4≤trianglesAt H t := by
    rcases (show t=a ∨ t=c ∨ t=w by simpa only [mem_insert,mem_singleton] using tm) with h|h|h
    · exact h ▸ sa
    · exact h ▸ sc
    · exact h ▸ sw
  refine ⟨score,?_⟩
  apply Nat.le_of_not_gt; intro low
  have range : H.degree t=0 ∨ H.degree t=1 ∨ H.degree t=2 ∨ H.degree t=3 := by omega
  have cap := Repair.triangles_le_choose H t
  have up : (H.degree t).choose 2≤3 := by rcases range with h|h|h|h <;> rw [h] <;> decide
  omega

end Graffiti384b.CubicShore
#print axioms Graffiti384b.CubicShore.third_score
#print axioms Graffiti384b.CubicShore.square_profile
