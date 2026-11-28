import BalancedOmissions

namespace Graffiti384b.OddStars
open Finset SimpleGraph PositivePalette LowSample
open private LowSample.two_degree from LowSample384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the degree-two-zero branch, the high vertices are exactly the vertices
of score at least two, in every star patch including the empty one. -/
theorem high_description (bad : bound G<gamma G) {z : V} (zz : trianglesAt G z=0)
    (dz : G.degree z=2) (S : Finset V) :
    high (patch G S)=high G ∧ ∀v,v∈high G ↔ 2≤trianglesAt G v := by
  have ones := (zero_two_forces_ears G bad zz dz).2
  have rich (v : V) (vm : v∈high G) : 2≤trianglesAt G v := by
    have dg := (mem_filter.mp vm).2
    by_contra! small
    rcases (show trianglesAt G v=0 ∨ trianglesAt G v=1 by omega) with h|h
    · have := zero_degree G bad h; omega
    · have := ones v h; omega
  have sub : high (patch G S)⊆high G := by
    intro v vm
    have inc : (patch G S).neighborFinset v⊆G.neighborFinset v :=
      fun _ m => (G.mem_neighborFinset ..).mpr (((patch G S).mem_neighborFinset ..).mp m).1
    have n := card_le_card inc
    simp only [card_neighborFinset_eq_degree] at n
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp vm).2.trans n⟩
  exact ⟨Subset.antisymm sub (fun v vm => rich_high G (rich v vm) _),
    fun v => ⟨rich v,fun h => sub (rich_high G h _)⟩⟩

theorem two_frames (bad : bound G<gamma G) {z f : V} (zz : trianglesAt G z=0)
    (dz : G.degree z=2) (sf : trianglesAt G f=1) :
    let H := high G
    let J := patch G {z}
    Covered J (insert z H) ∧ Covered (patch G ∅) (insert f H) ∧
    2*gamma G+(H.card+1)=2*Fintype.card V ∧ (types G).card=H.card+2 := by
  classical
  have ⟨hJ,cls⟩ := high_description G bad zz dz {z}
  have hC := (high_description G bad zz dz ∅).1
  have no : f∉high G := fun m => by have := (cls f).mp m; omega
  have sr := (zero_two_forces_ears G bad zz dz).2 f sf
  have edge : (patch G ∅).degree f=2 := by
    have p : 0<trianglesAt (patch G ∅) f := by rw [patch_scores,sf]; decide
    obtain ⟨a,b,fa,fb,ab⟩ := (TrianglePrune.triangle_iff _ _).mp p
    have low := Prerequisites.deg2 _ ab.ne fa fb
    have small : (patch G ∅).degree f≤2 := by
      by_contra! large; exact no (hC ▸ mem_filter.mpr ⟨mem_univ _,large⟩)
    omega
  have cf := cover_two G (S:=∅) (c:=f) (e:=f) (empty_subset _) edge
  have rep := represents_of_high G (S:=∅) (W:=insert f (high (patch G ∅))) (subset_insert ..)
    (fun _ => ⟨f,mem_insert_self ..,sf⟩)
  have ⟨im,inj,eq⟩ := rigid G (J:=patch G ∅) (fun _ _ h => h.1) rep cf bad
  rw [hC,card_insert_of_not_mem no] at eq
  have num := card_image_of_injOn inj
  rw [im,hC,card_insert_of_not_mem no,card_erase_of_mem (failure_requires_odd_zero G bad).2] at num
  have dzJ := (center_degree G (mem_singleton_self z)).trans dz
  have cz := cover_two G (S:={z}) (c:=z) (e:=z) (singleton_subset_iff.mpr (mem_insert_self ..)) dzJ
  rw [hJ] at cz
  rw [hC] at cf
  exact ⟨cz,cf,eq,by omega⟩

private theorem no_zero_neighbor {u v : V} (du : G.degree u=2) (su : trianglesAt G u=1)
    (sv : trianglesAt G v=0) : ¬G.Adj u v := by
  obtain ⟨a,b,nb,ua,ub,ab⟩ := Prerequisites.ear_pair G du (by omega : 0<trianglesAt G u)
  intro uv
  have m := (G.mem_neighborFinset ..).mpr uv
  rw [nb,mem_insert,mem_singleton] at m
  rcases m with rfl|rfl
  · have := (TrianglePrune.triangle_iff G _).mpr ⟨u,b,ua.symm,ab,ub⟩; omega
  · have := (TrianglePrune.triangle_iff G _).mpr ⟨u,a,ub.symm,ab.symm,ua⟩; omega

/-- Every degree-two vertex has both neighbors among the distinct rich
vertices. This covers the zero-score and the count-one degree-two vertices. -/
theorem contacts_high (bad : bound G<gamma G) {z : V} (zz : trianglesAt G z=0)
    (dz : G.degree z=2) {v : V} (dv : G.degree v=2) :
    G.neighborFinset v⊆high G := by
  obtain ⟨has,ones⟩ := zero_two_forces_ears G bad zz dz
  obtain ⟨f,_,sf⟩ := mem_image.mp has
  obtain ⟨cz,cf,eq,_⟩ := two_frames G bad zz dz sf
  have h := (high_description G bad zz dz ∅).2
  have zn : z∉high G := fun m => by have := (h z).mp m; omega
  have fn' : f∉high G := fun m => by have := (h f).mp m; omega
  have vn : v∉high G := fun m => by have := (mem_filter.mp m).2; omega
  have use {c : V} (cn : c∉high G) (vc : v≠c) (cut : Covered G (insert c (high G)))
      (noEdge : ¬G.Adj v c) : G.neighborFinset v⊆high G := by
    have ti : 2*gamma G+(insert c (high G)).card=2*Fintype.card V := by rwa [card_insert_of_not_mem cn]
    have out : v∉insert c (high G) := by simp [vc,vn]
    have allN := all_neighbors_protected G ti cut out dv
    intro w wm
    exact (mem_insert.mp (allN wm)).resolve_left (fun wc => noEdge (wc ▸ (G.mem_neighborFinset ..).mp wm))
  by_cases zero : trianglesAt G v=0
  · apply use fn' (fun ve => by rw [ve,sf] at zero; contradiction)
      (covered_mono G (J:=patch G ∅) (fun _ _ a => a.1) cf)
    exact fun vf => no_zero_neighbor G (ones f sf) sf zero vf.symm
  · have vs : trianglesAt G v=1 := by
      by_contra! n
      have := (h v).mpr (by omega); exact vn this
    exact use zn (fun ve => by rw [ve,zz] at vs; contradiction)
      (covered_mono G (J:=patch G {z}) (fun _ _ a => a.1) cz) (no_zero_neighbor G dv vs zz)

/-- At most one of all endpoint incidences at degree-two vertices can be
a repetition. In particular a repeated anchor has multiplicity exactly two. -/
theorem endpoint_count (bad : bound G<gamma G) {z : V} (zz : trianglesAt G z=0) (dz : G.degree z=2) :
    2*(twos G).card≤((high G).filter (fun u => ∃v∈twos G,G.Adj v u)).card+1 := by
  obtain ⟨f,_,sf⟩ := mem_image.mp (zero_two_forces_ears G bad zz dz).1
  have gap := (two_frames G bad zz dz sf).2.2.2
  let E := twos G
  by_contra! small
  apply (not_lt_of_ge (Repair.exact_of_low_support G E
    (disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2))
    (fun _ m => (LowSample.two_degree G m).ge) ?_ ?_)) bad
  · intro v vm w wm vw
    exact (mem_sdiff.mp wm).2 (contacts_high G bad zz dz (LowSample.two_degree G vm)
      ((G.mem_neighborFinset ..).mpr vw))
  · dsimp [E]; omega

end Graffiti384b.OddStars
#print axioms Graffiti384b.OddStars.two_frames
#print axioms Graffiti384b.OddStars.contacts_high
#print axioms Graffiti384b.OddStars.endpoint_count