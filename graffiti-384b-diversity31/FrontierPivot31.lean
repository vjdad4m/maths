import FrontierCore31

namespace Graffiti384b.Frontier31
open Finset SimpleGraph EarFrame33
open private CliquePivot33.isolated_degree from CliquePivot33
open private Repair.isolate from Repair384b
open private CubicShore.half_tight from CubicDiamondCut33
open private EarFrame33.merge_shared from EarFrame33
open private Repair.triangles_le_choose from Repair384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The unique nonedge in the four neighbors determines opposite pairs
which already give every pinned neighbor two neighbors of the other color. -/
theorem pivot_frame {x : V} (dx : H.degree x=4) (sx : trianglesAt H x=5) :
    ∃ P Q : Finset V,P∪Q=H.neighborFinset x ∧ P.card=2 ∧ Q.card=2 ∧ Frame H P Q ∧
      2≤nbr H x P ∧ 2≤nbr H x Q := by
  classical
  let N := H.neighborFinset x
  let E := BlockGeometry.gaps H N
  have sz : N.card=4 := (card_neighborFinset_eq_degree ..).trans dx
  have clock := BlockGeometry.gap_count H x
  change E.card+trianglesAt H x=(H.degree x).choose 2 at clock
  rw [dx,sx] at clock
  change E.card+5=6 at clock
  have single : E.card=1 := by omega
  obtain ⟨P,eq⟩ := card_eq_one.mp single
  have pm : P∈E := eq ▸ mem_singleton_self _
  have ⟨sub,ps⟩ := mem_powersetCard.mp (mem_filter.mp pm).1
  let Q := N\P
  have qs : Q.card=2 := by rw [show Q=N\P from rfl,card_sdiff sub,sz,ps]
  have un : P∪Q=N := union_sdiff_of_subset sub
  have dis : Disjoint P Q := disjoint_sdiff
  have cross (a : V) (am : a∈P) (b : V) (bm : b∈Q) : H.Adj a b := by
    obtain ⟨bn,bp⟩ := mem_sdiff.mp bm
    apply Classical.byContradiction; intro no
    have m := BlockGeometry.pair_gap H (sub am) bn (fun e => bp (e ▸ am)) no
    have same : {a,b}=P := mem_singleton.mp (eq ▸ m)
    exact bp (same ▸ (mem_insert_of_mem (mem_singleton_self b) : b∈({a,b}:Finset V)))
  have pins (D : Finset V) (szD : D.card=2) (w : V) (h : ∀ z∈D,H.Adj w z) : 2≤nbr H w D := by
    change 2≤(D.filter (H.Adj w)).card
    rw [filter_true_of_mem h,szD]
  refine ⟨P,Q,un,ps,qs,⟨dis,fun a am => pins Q qs a (cross a am),
    fun b bm => pins P ps b (fun a am => (cross a am b bm).symm)⟩,?_,?_⟩
  · exact pins P ps x (fun a am => (H.mem_neighborFinset ..).mp (sub am))
  · exact pins Q qs x (fun a am => (H.mem_neighborFinset ..).mp (mem_sdiff.mp am).1)

/-- In a half-tight graph containing this pivot, every protected coloring
covering the vertices below degree three uses two or more neighbors of x. -/
theorem frame_hits {x : V} (dx : H.degree x=4) (sx : trianglesAt H x=5)
    (half : Fintype.card V≤2*gamma H) {A B : Finset V} (frame : Frame H A B)
    (protect : ∀ w,w∉A∪B → 3≤H.degree w) : 2≤((A∪B)∩H.neighborFinset x).card := by
  classical
  obtain ⟨P,Q,un,_,_,base,px,qx⟩ := pivot_frame H dx sx
  by_contra! small
  have off : x∉A∪B := by
    intro m
    have inc (D : Finset V) (sub : D⊆A∪B) : D.filter (H.Adj x)⊆(A∪B)∩H.neighborFinset x :=
      fun z zm => mem_inter.mpr ⟨sub (mem_filter.mp zm).1,(H.mem_neighborFinset ..).mpr (mem_filter.mp zm).2⟩
    rcases mem_union.mp m with a|b
    · have h := (frame.2.1 x a).trans (card_le_card (inc B subset_union_right)); omega
    · have h := (frame.2.2 x b).trans (card_le_card (inc A subset_union_left)); omega
  have xn := H.not_mem_neighborFinset_self x
  have free (v : V) (away : v∉A∪B) (ne : v≠x) (np : v∉P) (nq : v∉Q) :
      3≤(Repair.isolate H x).degree v+2*(if v∈(∅:Finset V) then 1 else 0) := by
    have no : x∉H.neighborFinset v := by
      intro vx
      have vn := (H.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp vx).symm
      rw [←un] at vn
      exact (mem_union.mp vn).elim np nq
    simpa [CliquePivot33.isolated_degree H ne,erase_eq_of_not_mem no] using protect v away
  have obstruction := EarFrame33.merge_shared H ∅ frame base.1 (by rw [un]; omega) off
    (fun h => xn (un ▸ mem_union_left Q h)) (fun h => xn (un ▸ mem_union_right P h))
    px qx base.2.1 base.2.2 free
  exact obstruction (CubicShore.half_tight H half)

/-- The core has exactly one vertex of degree two. Its score is one.
Every compatible pair of protected color classes covering that ear must
meet the pivot neighborhood at least twice. -/
theorem ear_barrier {x : V} (dx : H.degree x=4) (sx : trianglesAt H x=5)
    (half : Fintype.card V≤2*gamma H) (pos : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) :
    ∃ e,H.degree e=2 ∧ trianglesAt H e=1 ∧ (∀ v,v≠e → 3≤H.degree v) ∧
      ∀ A B : Finset V,Frame H A B → e∈A∪B → 2≤((A∪B)∩H.neighborFinset x).card := by
  classical
  have low : ∃ e,H.degree e<3 := by
    by_contra! no
    have empty : Frame H ∅ ∅ := by simp [Frame]
    have h := frame_hits H dx sx half empty (fun w _ => no w)
    simp at h
  obtain ⟨e,de⟩ := low
  have val (v : V) (low : H.degree v<3) : H.degree v=2 ∧ trianglesAt H v=1 := by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    have deg := OneEar.deg2 H ab.ne va vb
    have eq : H.degree v=2 := by omega
    have small := Repair.triangles_le_choose H v
    rw [eq] at small; change trianglesAt H v≤1 at small
    have := pos v; exact ⟨eq,by omega⟩
  obtain ⟨d,s⟩ := val e de
  have rest (v : V) (ve : v≠e) : 3≤H.degree v := Nat.le_of_not_gt
    (fun h => ve (inj ((val v h).2.trans s.symm)))
  exact ⟨e,d,s,rest,fun A B f em => frame_hits H dx sx half f
    (fun w wm => rest w (fun eq => wm (eq ▸ em)))⟩

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.pivot_frame
#print axioms Graffiti384b.Frontier31.frame_hits
#print axioms Graffiti384b.Frontier31.ear_barrier
