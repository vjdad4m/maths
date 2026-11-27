import CoverClique31
namespace Graffiti384b.Cover31
open Finset SimpleGraph BlockGeometry LowSample
open private Frontier31.local_clique from Frontier31Finish
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Remove a cubic neighbor and cover each remaining missing edge by one vertex.
For a dense vertex of degree at most nine the thresholds leave six mutually adjacent neighbors. -/
theorem local_cap (t : (types G).card=31) (h : (high G).card=30) (bad : bound G<gamma G)
    (x : V) (hi : G.degree x≤9) : trianglesAt G x≤RankTable.cap (G.degree x) 3 := by
  classical
  apply Nat.le_of_not_gt
  intro dense
  obtain ⟨C,cl,xc⟩ := Frontier31.local_clique G hi dense
  obtain ⟨u,du,ux⟩ := adjacent G t h bad cl xc
  let N := G.neighborFinset x
  let S := N.erase u
  let M := S\(G.neighborFinset u).erase x
  let F := M.image (fun y => ({u,y}:Finset V))
  let E := gaps G N
  have un : u∈N := (G.mem_neighborFinset _ _).mpr ux.symm
  have xu : x∈G.neighborFinset u := (G.mem_neighborFinset _ _).mpr ux
  have xn : x∉N := G.not_mem_neighborFinset_self _
  have sc : S.card=G.degree x-1 := by rw [show S=N.erase u from rfl,card_erase_of_mem un,card_neighborFinset_eq_degree]
  have rc : ((G.neighborFinset u).erase x).card=2 := by rw [card_erase_of_mem xu,card_neighborFinset_eq_degree,du]
  have ml : G.degree x-3≤M.card := by
    have z := le_card_sdiff ((G.neighborFinset u).erase x) S
    change S.card-((G.neighborFinset u).erase x).card≤M.card at z
    omega
  have fs : F⊆E := by
    intro p pm
    obtain ⟨y,ym,rfl⟩ := mem_image.mp pm
    obtain ⟨ys,yr⟩ := mem_sdiff.mp ym
    obtain ⟨yu,yn⟩ := mem_erase.mp ys
    exact pair_gap G un yn yu.symm (fun uy => yr (mem_erase.mpr ⟨fun eq => xn (eq ▸ yn),(G.mem_neighborFinset _ _).mpr uy⟩))
  have fc : F.card=M.card := by
    apply card_image_of_injOn
    intro a am b _ eq
    have au := (mem_erase.mp (mem_sdiff.mp am).1).1
    change ({u,a}:Finset V)={u,b} at eq
    have m : a∈({u,b}:Finset V) := by rw [←eq]; exact mem_insert_of_mem (mem_singleton_self a)
    exact mem_singleton.mp ((mem_insert.mp m).resolve_left au)
  have fcap := card_le_card fs
  have total : E.card+trianglesAt G x=(G.degree x).choose 2 := gap_count G x
  let U := E\F
  have space : 6+U.card≤S.card := by
    have count : U.card=E.card-F.card := card_sdiff fs
    have four : 4≤G.degree x := by
      have z := card_le_card (show C.erase x⊆G.neighborFinset x from fun y ym => (G.mem_neighborFinset ..).mpr
        (cl.1 xc (mem_erase.mp ym).2 (mem_erase.mp ym).1.symm))
      rw [card_erase_of_mem xc,cl.2,card_neighborFinset_eq_degree] at z; exact z
    rcases (show G.degree x=4 ∨ G.degree x=5 ∨ G.degree x=6 ∨ G.degree x=7 ∨ G.degree x=8 ∨ G.degree x=9 by omega) with d|d|d|d|d|d <;>
      rw [d] at dense total ml sc <;> norm_num [RankTable.cap,Nat.choose] at dense total ml sc <;> first | omega | (have := card_pos.mpr ml; omega)
  have nonempty (p : Finset V) (pm : p∈U) : p.Nonempty :=
    card_pos.mp (by rw [BlockGeometry.two G (mem_sdiff.mp pm).1]; decide)
  let H := U.attach.image (fun p => (nonempty p.val p.property).choose)
  have small : H.card≤U.card := (card_image_le).trans_eq card_attach
  have big : 6≤(S\H).card := by
    have z := le_card_sdiff H S
    omega
  obtain ⟨K,ks,sz⟩ := exists_subset_card_eq big
  have adj (a : V) (ac : a∈K) (b : V) (bc : b∈K) (ab : a≠b) : G.Adj a b := by
    apply Classical.byContradiction
    intro miss
    obtain ⟨as',ah⟩ := mem_sdiff.mp (ks ac)
    obtain ⟨bs',bh⟩ := mem_sdiff.mp (ks bc)
    let p : Finset V := {a,b}
    have no : p∉F := by
      intro m
      obtain ⟨y,_,eq⟩ := mem_image.mp m
      have um : u∈p := eq ▸ mem_insert_self u {y}
      rcases mem_insert.mp um with ua|ub
      · exact (mem_erase.mp as').1 ua.symm
      · exact (mem_erase.mp bs').1 (mem_singleton.mp ub).symm
    have pm : p∈U := mem_sdiff.mpr ⟨pair_gap G (mem_erase.mp as').2 (mem_erase.mp bs').2 ab miss,no⟩
    have yes : (nonempty p pm).choose∈H := mem_image.mpr ⟨⟨p,pm⟩,mem_attach _ _,rfl⟩
    rcases mem_insert.mp (nonempty p pm).choose_spec with eq|eq
    · exact ah (eq ▸ yes)
    · exact bh ((mem_singleton.mp eq) ▸ yes)
  have kn : K⊆N := ks.trans (sdiff_subset.trans (erase_subset _ _))
  apply seven_free G t h bad (insert x K)
  refine ⟨?_,?_⟩
  · intro a am b bm ab
    rcases mem_insert.mp am with rfl|aa
    · rcases mem_insert.mp bm with rfl|bb
      · exact (ab rfl).elim
      · exact (G.mem_neighborFinset _ _).mp (kn bb)
    · rcases mem_insert.mp bm with rfl|bb
      · exact ((G.mem_neighborFinset _ _).mp (kn aa)).symm
      · exact adj _ aa _ bb ab
  · rw [card_insert_of_not_mem (fun z => xn (kn z)),sz]

/-- The branch with at least 31 nonleaves with 30 vertices of degree at least three satisfies #384b. -/
theorem exact_thirty (t : (types G).card=31) (q : 31≤(nonleaves G).card)
    (h : (high G).card=30) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨u,uc⟩ := Frontier31.one_center G t q bad
  exact (not_lt_of_ge (local_cap G t h bad u (by have := uc.2.1; omega))) uc.2.2.1

/-- At every nonleaf quota the catalogue bound holds for a connected graph
with 31 triangle-count types and 30 vertices of degree at least three. -/
theorem connected_thirty (conn : G.Connected) (t : (types G).card=31)
    (h : (high G).card=30) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  have caps := local_cap G t h bad
  have q := (Frontier31.profile G t caps bad).1
  obtain ⟨e,de,_,_⟩ := Frontier31.original_ear G conn t caps bad
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have eq := eq_of_subset_of_card_le sub (by omega)
  have eh : e∈high G := eq ▸ (show e∈nonleaves G from mem_filter.mpr ⟨mem_univ _,de.ge⟩)
  have z : 3≤G.degree e := (mem_filter.mp eh).2
  omega

/-- At 32 nonleaves, a diversity-31 failure must have exactly three
degree-two vertices and 29 vertices of degree at least three. -/
theorem residual (t : (types G).card=31) (q : (nonleaves G).card=32) (bad : bound G<gamma G) :
    (high G).card=29 ∧ (twos G).card=3 := by
  have lim := type_bound G
  have miss : ((high G).card+1)/2 < ((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) bad)
  have ne : (high G).card≠30 := fun z => (not_lt_of_ge (exact_thirty G t (by omega) z)) bad
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have count : (twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  omega

/-- All remaining connected diversity-31 obstructions have the maximal two
extra types over their 29 high vertices, at every order and nonleaf quota. -/
theorem failure_profile (conn : G.Connected) (t : (types G).card=31) (bad : bound G<gamma G) :
    (high G).card=29 ∧ Set.InjOn (trianglesAt G) (high G) ∧
      (∀ v∈high G,2≤trianglesAt G v) ∧ 0∈types G ∧ 1∈types G := by
  have lim := type_bound G
  have miss : ((high G).card+1)/2 < ((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) bad)
  have ne : (high G).card≠30 := fun z => (not_lt_of_ge (connected_thirty G conn t z)) bad
  exact ⟨by omega,Repair.maximal_diversity G (by omega)⟩

end Graffiti384b.Cover31
#print axioms Graffiti384b.Cover31.local_cap
#print axioms Graffiti384b.Cover31.connected_thirty
#print axioms Graffiti384b.Cover31.exact_thirty
#print axioms Graffiti384b.Cover31.residual
#print axioms Graffiti384b.Cover31.failure_profile
