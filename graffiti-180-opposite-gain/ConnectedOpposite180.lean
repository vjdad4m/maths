import LowerWing180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For two connected active regions with nonempty, incompatible terminal
masks, the allowance is at least three whenever no nonroot independent
mark has degree two. The root distance and marking of the
second tip are unrestricted. -/
theorem connected_opposite_gain (G : SimpleGraph V) (gc : G.Connected) (r a b : V) (ar : a≠r)
    (p : Bool) (A : Finset V) (ai : Indep G A) (ab : a≠b) (na : ¬G.Adj a b)
    (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p))
    (deg : G.degree a=4) (C D O : Finset V) (h : TwoRegions G a b C D O) (cc : Con G C) (dc : Con G D)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (left : ∃ t,DropCheck G a b (A∩insert r (parity G r p)) C c t)
    (right : ∃ t,DropCheck G a b (A∩insert r (parity G r p)) D c t)
    (absent : ¬∃ t,DropCheck G a b (A∩insert r (parity G r p)) C c t ∧
       DropCheck G a b (A∩insert r (parity G r p)) D c t)
    (high : ∀ v∈A,v≠r → G.degree v≠2) : 3≤allowance G r p A := by
  classical
  by_cases db : G.dist b r=G.dist a r+2
  swap
  · exact opposite_forces_three G gc r a b ar p A ai ab na bi ak bk deg C D O h c cp lc rc left right absent high db
  have hi : 2<Fintype.card V := by have := G.degree_lt_card_verts a;omega
  have am := (mem_inter.mp ak).1
  have ap := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  have bp : b∈parity G r p := (mem_parity ..).mpr (by have e := (mem_parity ..).mp ap;omega)
  have bm : b∉A := fun m => bk (mem_inter.mpr ⟨m,mem_insert_of_mem bp⟩)
  have br : b≠r := fun e => by rw [e,dist_self] at db;omega
  have paid := protected_degree G gc hi r a p A ai ak
  by_contra! small
  have sat : G.degree a=allowance G r p A+2 := by omega
  obtain ⟨z,bz,dz⟩ := Graffiti169.exists_predecessor G gc r b br
  have za := outside_predecessors_marked G gc (by omega) r a ar p A ai am sat br na bp bm bz dz
  have zp : z∉parity G r p := fun m => by have e := eq_dist G gc r b z p bz (iff_of_true bp m);omega
  have zr : z≠r := fun e => by rw [e,dist_self] at dz;omega
  have zh : 3≤G.degree z := by
    have up := forward_degree G gc r z b zr bz.symm (by omega)
    have notTwo := high _ za zr;omega
  obtain ⟨w,_,aw,zw,_,_,_,_,_⟩ := paired_ports G gc (by omega) r a z ar zr p A ai am ap za zp sat zh (by omega)
  let R := univ\({a,b}:Finset V)
  have zm : z∈R := mem_sdiff.mpr ⟨mem_univ _,fun m => by
    rcases mem_insert.mp m with e|e
    · rw [e] at dz;omega
    · rw [mem_singleton.mp e] at dz;omega⟩
  have wm : w∈R := mem_sdiff.mpr ⟨mem_univ _,fun e => (mem_insert.mp e).elim (fun t => aw.ne t.symm)
    (fun m => na ((mem_singleton.mp m) ▸ aw))⟩
  have cs : C⊆R := by change C⊆univ\({a,b}:Finset V);rw [h.partition];exact subset_union_left.trans subset_union_left
  have ds : D⊆R := by change D⊆univ\({a,b}:Finset V);rw [h.partition];exact subset_union_right.trans subset_union_left
  have cClosed (i : V) (ic : i∈C) (j : V) (jm : j∈R) (edge : G.Adj i j) : j∈C := by
    change j∈univ\({a,b}:Finset V) at jm;rw [h.partition] at jm
    rcases mem_union.mp jm with cd|o
    · exact (mem_union.mp cd).resolve_right (fun jd => h.cross i ic j jd edge)
    · exact (h.out i (mem_union_left _ ic) j o edge).elim
  have dClosed (i : V) (id : i∈D) (j : V) (jm : j∈R) (edge : G.Adj i j) : j∈D := by
    change j∈univ\({a,b}:Finset V) at jm;rw [h.partition] at jm
    rcases mem_union.mp jm with cd|o
    · exact (mem_union.mp cd).resolve_left (fun jc => h.cross j jc i id edge.symm)
    · exact (h.out i (mem_union_right _ id) j o edge).elim
  have contacts := opposite_contacts G a b ab na A _ ai am inter_subset_left deg C D O h c cp lc rc left right absent
  have sum := region_sum G a C D h.apart
  have lcnt := mixed_count G a C c lc
  have dcnt := mixed_count G a D c rc
  change w∈univ\({a,b}:Finset V) at wm;rw [h.partition] at wm
  have wing := (mem_union.mp wm).resolve_right (fun wo => h.inactive w wo aw)
  rcases mem_union.mp wing with wc|wd
  · have cap := lower_wing G gc (by omega) r a b z ar p A ai am ap bm bp na sat db bz dz high C cc cs
      (cClosed w wc z zm zw.symm) cClosed (by omega)
    have lo := contacts.1;omega
  · have cap := lower_wing G gc (by omega) r a b z ar p A ai am ap bm bp na sat db bz dz high D dc ds
      (dClosed w wd z zm zw.symm) dClosed (by omega)
    have lo := contacts.2.1;omega

/-- A genuinely opposite pair of masks at the exact allowance two
requires a nonroot independently marked vertex of degree exactly two. -/
theorem tight_opposite_has_degree_two (G : SimpleGraph V) (gc : G.Connected) (r a b : V) (ar : a≠r)
    (p : Bool) (A : Finset V) (ai : Indep G A) (ab : a≠b) (na : ¬G.Adj a b)
    (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p))
    (deg : G.degree a=4) (C D O : Finset V) (h : TwoRegions G a b C D O) (cc : Con G C) (dc : Con G D)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (left : ∃ t,DropCheck G a b (A∩insert r (parity G r p)) C c t)
    (right : ∃ t,DropCheck G a b (A∩insert r (parity G r p)) D c t)
    (absent : ¬∃ t,DropCheck G a b (A∩insert r (parity G r p)) C c t ∧
       DropCheck G a b (A∩insert r (parity G r p)) D c t)
    (two : allowance G r p A=2) : ∃ v∈A,v≠r ∧ G.degree v=2 := by
  by_contra! no
  have gain := connected_opposite_gain G gc r a b ar p A ai ab na bi ak bk deg C D O h cc dc c cp lc rc left right absent no
  omega

#print axioms connected_opposite_gain
#print axioms tight_opposite_has_degree_two
end Minimal180.OppositeGain
