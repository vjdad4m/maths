import FourFan28
namespace Graffiti384b.Four28
open Finset SimpleGraph EarFrame33
open private EarFrame33.merge_shared from EarFrame33
open private Repair.nbr_mono Repair.isolate from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
open private CubicShore.half_tight from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A cubic obstruction must miss part of the central triangle. Cubics seeing
all three central vertices can be pinned with the two tips of the fan. -/
theorem wheel_blocker {A B T Y : Finset V} (fr : Frame G A B) (fan : Fan G T Y)
    (low : ∀ v,v∉A∪B → 3≤G.degree v) (tight : Fintype.card V≤2*gamma G)
    (over : ((A∪B)∩(T∪Y)).card≤1) {z : V} (zt : z∈T) (off : z∉A∪B) :
    ∃ u,u∉A∪B ∧ u∉T∪Y ∧ G.degree u=3 ∧ G.Adj u z ∧ ∃ t∈T,¬G.Adj u t := by
  classical
  obtain ⟨cl,yc,dis,cross⟩ := fan
  let L := T.erase z
  let E := univ.filter (fun u => u∉A∪B ∧ u∉T∪Y ∧ G.degree u=3 ∧ G.Adj u z)
  let R := Y∪E
  have lc : L.card=2 := by rw [show L=T.erase z from rfl,card_erase_of_mem zt,cl.2]
  have see {v : V} {D : Finset V} (dc : D.card=2) (edges : ∀ d∈D,G.Adj v d) :
      2≤nbr G v D := by simp [nbr,filter_true_of_mem edges,dc]
  have inc : L⊆T := erase_subset ..
  have zr : z∉R := by
    intro m
    rcases mem_union.mp m with zy|ze
    · exact disjoint_left.mp dis zt zy
    · exact (mem_filter.mp ze).2.2.1 (mem_union_left Y zt)
  have lr : Disjoint L R := disjoint_left.mpr (by
    intro u ul ur
    rcases mem_union.mp ur with uy|ue
    · exact disjoint_left.mp dis (inc ul) uy
    · exact (mem_filter.mp ue).2.2.1 (mem_union_left Y (inc ul)))
  have overlap : ((A∪B)∩(L∪R)).card≤1 := (card_le_card
    (show (A∪B)∩(L∪R)⊆(A∪B)∩(T∪Y) from by
      intro u m
      obtain ⟨uf,h⟩ := mem_inter.mp m
      apply mem_inter.mpr ⟨uf,?_⟩
      rcases mem_union.mp h with ul|ur
      · exact mem_union_left Y (inc ul)
      · rcases mem_union.mp ur with uy|ue
        · exact mem_union_right T uy
        · exact ((mem_filter.mp ue).2.1 uf).elim)).trans over
  by_contra! none
  have protect (u : V) (ue : u∈E) (v : V) (vt : v∈T) : G.Adj u v := by
    obtain ⟨uf,uo,du,uz⟩ := (mem_filter.mp ue).2
    exact none u uf uo du uz v vt
  apply (EarFrame33.merge_shared G ∅ fr lr overlap off (by simp [L]) zr
    (see lc (fun a am => cl.1 zt (inc am) (mem_erase.mp am).1.symm))
    ((see yc (cross z zt)).trans (Repair.nbr_mono G z subset_union_left))
    (fun u ul => (see yc (cross u (inc ul))).trans (Repair.nbr_mono G u subset_union_left))
    (fun v vr => see lc (fun u ul => (mem_union.mp vr).elim
      (fun vy => (cross u (inc ul) v vy).symm) (fun ve => protect v ve u (inc ul))))
    ?_) (CubicShore.half_tight G tight)
  intro v vf vz vl vr
  simp only [Finset.not_mem_empty,ite_false,Nat.mul_zero,Nat.add_zero]
  rw [CliquePivot33.isolated_degree G vz]
  by_cases edge : G.Adj v z
  · rw [card_erase_of_mem ((G.mem_neighborFinset ..).mpr edge),card_neighborFinset_eq_degree]
    have vo : v∉T∪Y := fun m => (mem_union.mp m).elim (fun vt => vl (mem_erase.mpr ⟨vz,vt⟩))
      (fun vy => vr (mem_union_left _ vy))
    have ne : G.degree v≠3 := fun eq => vr (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,vf,vo,eq,edge⟩))
    have := low v vf; omega
  · rw [erase_eq_of_not_mem (fun m => edge ((G.mem_neighborFinset ..).mp m)),card_neighborFinset_eq_degree]
    exact low v vf

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.wheel_blocker
