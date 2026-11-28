import PosaCrossCycle189
import PosaBridgeAdapter189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath Graffiti189LongestPath.PosaSpliceCommon Graffiti189LongestPath.PosaMaxCover
open Graffiti189LongestPath.PosaCycleCover Graffiti189LongestPath.PosaCrossCycle
open Graffiti189LongestPath.PosaBridgeAdapter
open private Graffiti189LongestPath.no_endpoints from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 7500000
namespace Graffiti189LongestPath.PosaEndpointCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Interior spine indices adjacent to a specified vertex. -/
def innerNeighbors {a b : V} (p : G.Walk a b) (v : V) : Finset Nat :=
  (range p.length).filter (fun i => 0<i ∧ G.Adj v (p.getVert i))

omit [Fintype V] [DecidableEq V] in
theorem mem_innerNeighbors {a b : V} (p : G.Walk a b) (v : V) (i : Nat) :
    i∈innerNeighbors p v ↔ 0<i ∧ i<p.length ∧ G.Adj v (p.getVert i) := by
  simp [innerNeighbors,mem_filter,mem_range,and_assoc,and_left_comm]

theorem innerNeighbors_count {a b : V} (p : G.Walk a b) (hp : p.IsPath) (v : V)
    (ha : ¬G.Adj v a) (hb : ¬G.Adj v b)
    (all : ∀ z,G.Adj v z → z∈p.support) : (innerNeighbors p v).card=G.degree v := by
  have eq : (innerNeighbors p v).image p.getVert=G.neighborFinset v := by
    ext z
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact (G.mem_neighborFinset _ _).mpr ((mem_innerNeighbors _ _ _).mp hi).2.2
    · intro h
      have ed := (G.mem_neighborFinset _ _).mp h
      obtain ⟨i,eq,il⟩ := mem_support_iff_exists_getVert.mp (all _ ed)
      have ip : 0<i := by
        apply Nat.pos_of_ne_zero
        intro e
        rw [e,getVert_zero] at eq
        exact ha (eq.symm ▸ ed)
      have iN : i<p.length := by
        apply lt_of_le_of_ne il
        intro e
        rw [e,getVert_length] at eq
        exact hb (eq.symm ▸ ed)
      exact mem_image.mpr ⟨i,(mem_innerNeighbors _ _ _).mpr ⟨ip,iN,eq.symm ▸ ed⟩,eq⟩
  have c := congrArg Finset.card eq
  have inj : Set.InjOn p.getVert (↑(innerNeighbors p v):Set Nat) := by
    intro i hi j hj e
    exact hp.getVert_injOn ((mem_innerNeighbors _ _ _).mp hi).2.1.le
      ((mem_innerNeighbors _ _ _).mp hj).2.1.le e
  rwa [card_image_of_injOn inj,G.card_neighborFinset_eq_degree] at c

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem beginning_neighbors_in_spine {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    ∀ z,G.Adj a z → z∈p.support := by
  intro z e
  apply Classical.byContradiction
  intro no
  exact (Graffiti189LongestPath.no_endpoints hp no).1 e.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ending_neighbors_in_spine {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    ∀ z,G.Adj b z → z∈p.support := by
  intro z e
  apply Classical.byContradiction
  intro no
  exact (Graffiti189LongestPath.no_endpoints hp no).2 e.symm

/-- Pósa's long cycle from a longest path with two high endpoints,
using the independent fact that a cycle spanning a longest spine
forces the spine to exhaust the whole connected graph. -/
theorem long_cycle_from_high_longest_path (m : Nat) (m2 : 2≤m)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (hiA : m≤G.degree a) (hiB : m≤G.degree b)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (full : ∀ z (c : G.Walk z z),c.IsCycle → p.length<c.length →
      (∀ w,w∈c.support ↔ w∈p.support) → ∀ w,w∈p.support) :
    ∃ z, ∃ c : G.Walk z z,c.IsCycle ∧ min (Fintype.card V) (2*m)≤c.length := by
  classical
  have ap := beginning_neighbors_in_spine hp
  have bp := ending_neighbors_in_spine hp
  have p2 : 2≤p.length := by
    have sub : G.neighborFinset a⊆p.support.toFinset.erase a := by
      intro z zn
      have edge := (G.mem_neighborFinset _ _).mp zn
      exact mem_erase.mpr ⟨edge.ne.symm,List.mem_toFinset.mpr (ap z edge)⟩
    have q := card_le_card sub
    rw [G.card_neighborFinset_eq_degree,card_erase_of_mem (List.mem_toFinset.mpr p.start_mem_support),
      List.toFinset_card_of_nodup hp.1.support_nodup,length_support,Nat.add_sub_cancel] at q
    omega
  have completes {z : V} (c : G.Walk z z) (cc : c.IsCycle)
      (len : p.length<c.length) (sup : ∀ w,w∈c.support ↔ w∈p.support) :
      min (Fintype.card V) (2*m)≤c.length := by
    have sc : p.support.toFinset=univ := by
      ext w
      simp only [List.mem_toFinset,mem_univ,iff_true]
      exact full z c cc len sup w
    have pc : p.support.toFinset.card=p.length+1 := by rw
      [List.toFinset_card_of_nodup hp.1.support_nodup,length_support]
    rw [sc,card_univ] at pc
    exact (min_le_left _ _).trans (by omega)
  by_cases edge : G.Adj a b
  · obtain ⟨c,cp,cl,cs⟩ := close_spine_path p hp.1 p2 edge
    exact ⟨b,c,cp,completes c cp (by omega) cs⟩
  have nedge : ¬G.Adj b a := fun e => edge e.symm
  let L := innerNeighbors p a
  let R := innerNeighbors p b
  let S := L.image (fun i => i-1)
  have lc : L.card=G.degree a := innerNeighbors_count p hp.1 a (G.loopless a) edge ap
  have rc : R.card=G.degree b := innerNeighbors_count p hp.1 b nedge (G.loopless b) bp
  have ls (i : Nat) (h : i∈L) := (mem_innerNeighbors p a i).mp h
  have rs (i : Nat) (h : i∈R) := (mem_innerNeighbors p b i).mp h
  by_cases dis : Disjoint S R
  · by_cases cross : ∃ i∈L,∃ j∈R,j<i
    · obtain ⟨i,iL,j,jR,ji,_,count⟩ := PosaCrossing189.exists_min_gap_card_kept
        (fun i h => ⟨(ls i h).1,(ls i h).2.1⟩)
        (fun j h => ⟨(rs j h).1,(rs j h).2.1⟩) dis cross
      have jj := rs j jR
      have ii := ls i iL
      obtain ⟨c,cp,_,cs⟩ := cycle_from_crossing p hp.1 i j jj.1 ji ii.2.1 ii.2.2 jj.2.2
      have bound := cycle_ge_index_card p hp.1 c cp (PosaCrossing189.kept p.length j i)
        (fun u h => (PosaCrossing189.mem_kept.mp h).elim (fun h => h.trans jj.2.1.le) And.right) cs
      exact ⟨_,c,cp,(min_le_right _ _).trans (by omega)⟩
    obtain ⟨W,best⟩ := exists_max_covered (ordered_pair_of_singleton_connected p hp.1 p2 conn)
    obtain ⟨c,cp,cs⟩ := cycle_of_ordered_pair W
    have iCap : (L∩R).card≤1 := by
      apply Nat.le_of_not_gt
      intro no
      obtain ⟨i,im,j,jm,ne⟩ := one_lt_card.mp no
      obtain ⟨il,ir⟩ := mem_inter.mp im
      obtain ⟨jl,jr⟩ := mem_inter.mp jm
      have ij : i≤j := Nat.le_of_not_gt (fun h => cross ⟨i,il,j,jr,h⟩)
      have ji : j≤i := Nat.le_of_not_gt (fun h => cross ⟨j,jl,i,ir,h⟩)
      exact ne (le_antisymm ij ji)
    let I := insert 0 (insert p.length (L∪R))
    have Range : ∀ i∈I,i≤p.length := by
      intro i h
      rcases mem_insert.mp h with rfl|h
      · omega
      rcases mem_insert.mp h with rfl|h
      · omega
      exact (mem_union.mp h).elim (fun h => (ls _ h).2.1.le) (fun h => (rs _ h).2.1.le)
    have Visit : ∀ i∈I,p.getVert i∈c.support := by
      intro i h
      apply (cs _).mpr
      rcases mem_insert.mp h with rfl|h
      · exact Or.inl (p.getVert_zero.symm ▸ W.left.start_mem_support)
      rcases mem_insert.mp h with rfl|h
      · exact Or.inl (p.getVert_length.symm ▸ W.left.end_mem_support)
      rcases mem_union.mp h with h|h
      · have q := ls _ h
        exact optimal_left hp.1 W best _ q.1 q.2.1 q.2.2
      · have q := rs _ h
        exact optimal_right hp.1 W best _ q.1 q.2.1 q.2.2
    have ny : p.length∉L∪R := by
      intro h
      exact (mem_union.mp h).elim (fun q => (Nat.lt_irrefl _) (ls _ q).2.1)
        (fun q => (Nat.lt_irrefl _) (rs _ q).2.1)
    have nz : 0∉insert p.length (L∪R) := by
      intro h
      rcases mem_insert.mp h with h|h
      · omega
      exact (mem_union.mp h).elim (fun q => (Nat.lt_irrefl _) (ls _ q).1)
        (fun q => (Nat.lt_irrefl _) (rs _ q).1)
    have cardI : I.card=(L∪R).card+2 := by
      rw [card_insert_of_not_mem nz,card_insert_of_not_mem ny]
    have unionI := card_union_add_card_inter L R
    have ge := cycle_ge_index_card p hp.1 c cp I Range Visit
    exact ⟨a,c,cp,(min_le_right _ _).trans (by omega)⟩
  have inter : ∃ j∈S,j∈R := by
    apply Classical.byContradiction
    intro no
    exact dis (disjoint_left.mpr (fun a ha hb => no ⟨a,ha,hb⟩))
  obtain ⟨j,jS,jR⟩ := inter
  obtain ⟨i,iL,ij⟩ := mem_image.mp jS
  have jj := rs j jR
  have ii := ls i iL
  obtain ⟨c,cp,sub,cs⟩ := cycle_from_crossing p hp.1 i j jj.1 (by omega) ii.2.1 ii.2.2 jj.2.2
  have all : ∀ i≤p.length,p.getVert i∈c.support := by
    intro t tN
    apply cs
    exact PosaCrossing189.mem_kept.mpr (by omega)
  have sup : ∀ w,w∈c.support ↔ w∈p.support := by
    intro w
    refine ⟨sub w,?_⟩
    intro hw
    obtain ⟨t,eq,tN⟩ := mem_support_iff_exists_getVert.mp hw
    exact eq ▸ all t tN
  have count := cycle_ge_index_card p hp.1 c cp (range (p.length+1))
    (fun t ht => by have q := mem_range.mp ht; omega)
    (fun t ht => all t (by have q := mem_range.mp ht; omega))
  rw [card_range] at count
  exact ⟨_,c,cp,completes c cp (by omega) sup⟩

#print axioms innerNeighbors_count
#print axioms long_cycle_from_high_longest_path
end Graffiti189LongestPath.PosaEndpointCycle
