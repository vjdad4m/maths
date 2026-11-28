import OddStarFrontier

namespace Graffiti384b.OddStars
open Finset SimpleGraph PositivePalette
open private Repair.omit_set Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem covered_mono {J : SimpleGraph V} [DecidableRel J.Adj] (le : J≤G)
    {W : Finset V} (cut : Covered J W) : Covered G W := by
  obtain ⟨A,h,k⟩ := cut
  have mono (v : V) (S : Finset V) : nbr J v S≤nbr G v S :=
    card_le_card (fun _ m => mem_filter.mpr ⟨(mem_filter.mp m).1,le (mem_filter.mp m).2⟩)
  exact ⟨A,fun v vm va => (h v vm va).trans (mono ..),fun v vm va => (k v vm va).trans (mono ..)⟩

/-- Under equality a degree-two vertex outside a protected set has a
neighbor on each of its two omission shores, for every protecting cut. -/
theorem split_neighbors {W A : Finset V} (tight : 2*gamma G+W.card=2*Fintype.card V)
    (left : ∀ v∈W,v∈A → 2≤nbr G v Aᶜ) (right : ∀ v∈W,v∈Aᶜ → 2≤nbr G v A)
    {z : V} (off : z∉W) (dz : 2≤G.degree z) :
    (W∩A).card=(W\A).card ∧ (∃ u∈W∩A,G.Adj z u) ∧ (∃v∈W\A,G.Adj z v) := by
  let L := W∩A
  let R := W\A
  have lf (v : V) (vm : v∈L) : 2≤nbr G v Lᶜ :=
    (left v (mem_inter.mp vm).1 (mem_inter.mp vm).2).trans (Repair.nbr_mono G _ (fun _ h =>
       mem_compl.mpr (fun m => mem_compl.mp h (mem_inter.mp m).2)))
  have rf (v : V) (vm : v∈R) : 2≤nbr G v Rᶜ :=
    (right v (mem_sdiff.mp vm).1 (mem_compl.mpr (mem_sdiff.mp vm).2)).trans (Repair.nbr_mono G _ (fun _ h =>
       mem_compl.mpr (fun m => (mem_sdiff.mp m).2 h)))
  have a := Repair.omit_set G L lf
  have b := Repair.omit_set G R rf
  have lc := card_le_univ L
  have rc := card_le_univ R
  have partition : R.card+L.card=W.card := card_sdiff_add_card_inter W A
  have eq : L.card=R.card := by omega
  have contact (S : Finset V) (sub : S⊆W) (size : S.card=L.card)
      (valid : ∀v∈S,2≤nbr G v Sᶜ) : ∃ v∈S,G.Adj z v := by
    by_contra! no
    have nz : z∉S := fun m => off (sub m)
    have big := Repair.omit_set G (insert z S) (by
      intro v vm
      rcases mem_insert.mp vm with rfl|vs
      · have inc : G.neighborFinset v ⊆ (insert v S)ᶜ.filter (G.Adj v) := by
          intro w wm
          have vw := (G.mem_neighborFinset ..).mp wm
          exact mem_filter.mpr ⟨mem_compl.mpr (fun m => (mem_insert.mp m).elim
            (fun e => vw.ne e.symm) (fun s => no w s vw)),vw⟩
        have num := card_le_card inc
        rw [card_neighborFinset_eq_degree] at num
        exact dz.trans num
      · apply (valid v vs).trans (card_le_card ?_)
        intro w wm
        obtain ⟨out,edge⟩ := mem_filter.mp wm
        exact mem_filter.mpr ⟨mem_compl.mpr (fun m => (mem_insert.mp m).elim
          (fun e => no v vs (e ▸ edge.symm)) (mem_compl.mp out)),edge⟩)
    have bound := card_le_univ (insert z S)
    rw [card_insert_of_not_mem nz] at big bound
    omega
  exact ⟨eq,contact L inter_subset_left rfl lf,contact R sdiff_subset eq.symm rf⟩

theorem all_neighbors_protected {W : Finset V} (tight : 2*gamma G+W.card=2*Fintype.card V)
    (cut : Covered G W) {z : V} (off : z∉W) (dz : G.degree z=2) :
    G.neighborFinset z⊆W := by
  obtain ⟨A,left,right⟩ := cut
  obtain ⟨_,⟨u,um,zu⟩,⟨v,vm,zv⟩⟩ := split_neighbors G tight left right off dz.ge
  have uv : u≠v := fun e => (mem_sdiff.mp vm).2 (e ▸ (mem_inter.mp um).2)
  have sub : ({u,v} : Finset V)⊆G.neighborFinset z :=
    insert_subset ((G.mem_neighborFinset ..).mpr zu) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr zv))
  have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,dz,card_pair uv])
  rw [←eq]
  exact insert_subset (mem_inter.mp um).1 (singleton_subset_iff.mpr (mem_sdiff.mp vm).1)

end Graffiti384b.OddStars
#print axioms Graffiti384b.OddStars.split_neighbors
#print axioms Graffiti384b.OddStars.all_neighbors_protected