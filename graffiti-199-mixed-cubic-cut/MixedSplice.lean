import PrescribedPaths
import MixedPortShape

open private two_distinct_contacts from TwoCliqueShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V]

namespace CubicMixedCut

variable (F : CubicMixedCut G)

omit [Fintype V] in
theorem r_only_in_A {x : V} (h : x ∈ F.A) (rx : G.Adj F.r x) : x = F.a := by
  rcases (F.neighbors x).mp rx with e|e|e
  · exact e
  · exact (F.apart_ne h F.bB e).elim
  · exact (F.apart_ne h F.cB e).elim

omit [Fintype V] in
theorem cut_size : ({F.r,F.p,F.q} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_not_mem (by simp [F.rp,F.rq]),Finset.card_pair F.pq]

omit [Fintype V] in
theorem other_contacts_of_B_edge {z x : V} (hz : z ∈ F.B) (zx : G.Adj z x) :
    x ∈ F.B ∨ x = F.r ∨ x = F.p ∨ x = F.q := by
  classical
  by_cases h : x ∈ F.B
  · exact Or.inl h
  · exact Or.inr (by simpa using F.boundB z hz x h zx)

theorem distinct_contacts_to_B (conn : ConnectivityAtLeast G 3) :
    ∃ x ∈ F.B, ∃ y ∈ F.B, x ≠ y ∧ G.Adj F.p x ∧ G.Adj F.q y := by
  classical
  have same : ({F.p,F.q,F.r} : Finset V) = {F.r,F.p,F.q} := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  exact two_distinct_contacts (G := G) (A := F.B) (p := F.p) (q := F.q) (r := F.r)
    conn (Ne.symm F.rp) (same.symm ▸ F.offB) (same.symm ▸ F.boundB)
    ⟨F.b,F.bB,F.c,F.cB,F.bc⟩

/-- Route the clique between the cubic port and one other port, then
traverse the nonclique side and end at the remaining port. -/
theorem finish_of_B_path (conn : ConnectivityAtLeast G 3) {x y : V}
    (Bpath : Traverses G F.B x y) (px : G.Adj F.p x) (qy : G.Adj F.q y) :
    Traceable G := by
  classical
  obtain ⟨a,aA,z,zA,az,ra,pz⟩ := two_distinct_contacts conn F.rq F.offA F.boundA
    ⟨F.a,F.aA,F.tail,F.tailA,F.aTail⟩
  have Apath := Traverses.clique F.cliqueA aA zA az
  have off1 : Disjoint ({F.r} : Set V) F.A := by
    apply Set.disjoint_left.mpr
    intro v vr ha
    exact F.r_not_A ((show v = F.r from vr) ▸ ha)
  have part1 := (Traverses.single (G := G) F.r).join Apath off1 ra
  have off2 : Disjoint (({F.r} : Set V) ∪ F.A) {F.p} := by
    apply Set.disjoint_left.mpr
    rintro v (vr|ha) vp
    · exact F.rp ((show v = F.r from vr).symm.trans (show v = F.p from vp))
    · exact F.offA F.p (by simp) ((show v = F.p from vp) ▸ ha)
  have part2 := part1.join (Traverses.single F.p) off2 pz.symm
  have off3 : Disjoint ((({F.r} : Set V) ∪ F.A) ∪ {F.p}) F.B := by
    apply Set.disjoint_left.mpr
    rintro v ((vr|ha)|vp) hb
    · exact F.r_not_B ((show v = F.r from vr) ▸ hb)
    · exact Set.disjoint_left.mp F.apart ha hb
    · exact F.offB F.p (by simp) ((show v = F.p from vp) ▸ hb)
  have part3 := part2.join Bpath off3 px
  have off4 : Disjoint (((({F.r} : Set V) ∪ F.A) ∪ {F.p}) ∪ F.B) {F.q} := by
    apply Set.disjoint_left.mpr
    rintro v (((vr|ha)|vp)|hb) vq
    · exact F.rq ((show v = F.r from vr).symm.trans (show v = F.q from vq))
    · exact F.offA F.q (by simp) ((show v = F.q from vq) ▸ ha)
    · exact F.pq ((show v = F.p from vp).symm.trans (show v = F.q from vq))
    · exact F.offB F.q (by simp) ((show v = F.q from vq) ▸ hb)
  have part4 := part3.join (Traverses.single F.q) off4 qy.symm
  have full : ((((({F.r} : Set V) ∪ F.A) ∪ {F.p}) ∪ F.B) ∪ {F.q}) = Set.univ := by
    ext v
    have h := F.cover v
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    tauto
  obtain ⟨P,_,_⟩ := part4
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ P⟩)

end CubicMixedCut

variable [DecidableRel G.Adj]

omit [Fintype V] in
theorem card_triple_le (x y z : V) : ({x,y,z} : Finset V).card ≤ 3 := by
  have hx := Finset.card_insert_le x ({y,z} : Finset V)
  have hy := Finset.card_insert_le y ({z} : Finset V)
  rw [Finset.card_singleton] at hy
  omega

theorem degree_le_three_of_three_names {v x y z : V}
    (only : ∀ u, G.Adj v u → u = x ∨ u = y ∨ u = z) : G.degree v ≤ 3 := by
  classical
  have subset : G.neighborFinset v ⊆ ({x,y,z} : Finset V) := by
    intro u hu
    simpa using only u ((G.mem_neighborFinset _ _).mp hu)
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card subset).trans (card_triple_le ..)

end Graffiti199Depleted.Catalogue
