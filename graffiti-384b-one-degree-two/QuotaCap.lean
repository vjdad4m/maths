import QuotaClique
namespace Graffiti384b.PivotQuota
open Finset SimpleGraph BlockGeometry LowSample
open private Quota29.local_clique from FrontierTwentyNine384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Remove a cubic neighbor and cover each remaining missing edge by one vertex.
For a dense vertex of degree at most eight the thresholds leave six mutually adjacent neighbors. -/
theorem local_cap (rel : (types G).card=(high G).card+1) (bad : bound G<gamma G)
    (x : V) (hi : G.degree x≤8) : trianglesAt G x≤RankTable.cap (G.degree x) 3 := by
  classical
  apply Nat.le_of_not_gt
  intro dense
  obtain ⟨C,cl,xc⟩ := Quota29.local_clique G hi dense
  obtain ⟨u,du,ux⟩ := adjacent G rel bad cl xc
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
    rcases (show G.degree x=4 ∨ G.degree x=5 ∨ G.degree x=6 ∨ G.degree x=7 ∨ G.degree x=8 by omega) with d|d|d|d|d <;>
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
  apply seven_free G rel bad (insert x K)
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

/-- With at least thirty nonleaves and twenty-eight high vertices, the
degree-eight local cap supplies the fifteenth omission. -/
theorem exact_high28 (t : (types G).card=29) (q : 30≤(nonleaves G).card)
    (h : (high G).card=28) : gamma G≤bound G := by
  by_contra! fail
  exact (not_lt_of_ge (Quota29.Local.exact_of_local_cap G t q
    (fun v dv => local_cap G (by omega) fail v dv))) fail

end Graffiti384b.PivotQuota
#print axioms Graffiti384b.PivotQuota.local_cap
#print axioms Graffiti384b.PivotQuota.exact_high28
