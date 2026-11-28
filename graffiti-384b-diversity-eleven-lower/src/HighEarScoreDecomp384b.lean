import DiversityElevenProfile384b
import ShorePairs

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph ShorePairs
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- When the low shore is independent and has degree at most two,
its triangles contribute exactly one at each of their high endpoints.
The weighted high graph thus retains the exact original scores. -/
theorem triangle_count_high_with_independent_ears (sup : Supported G)
    (H : Finset V) (small : ∀ x∉H, G.degree x≤2)
    (indep : ∀ x∉H, ∀ y∉H, ¬G.Adj x y) (v : H) :
    trianglesAt G v.val = trianglesAt (G.induce (H : Set V)) v + nbr G v.val Hᶜ := by
  classical
  let J := G.induce (H : Set V)
  let N := G.neighborFinset v.val
  let A := N∩H
  let B := N\H
  have AB : A∪B=N := by
    ext x
    simp only [A,B,mem_union,mem_inter,mem_sdiff]
    tauto
  have aj : ∀ e∈B, ∀ M⊆B, nbr G e (A∪M)=1 := by
    intro e eB M MB
    obtain ⟨eN,eout⟩ := mem_sdiff.mp eB
    have ve : G.Adj v.val e := (G.mem_neighborFinset ..).mp eN
    obtain ⟨z,vz,ez⟩ := sup ve
    have zH : z∈H := by by_contra z0; exact indep e eout z z0 ez
    have za : z∈A := mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr vz,zH⟩
    have n : G.neighborFinset e={v.val,z} := by
      symm
      apply eq_of_subset_of_card_le
      · exact insert_subset ((G.mem_neighborFinset ..).mpr ve.symm)
          (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ez))
      · rw [card_pair vz.ne,card_neighborFinset_eq_degree]
        exact small e eout
    have cnt : (A∪M).filter (G.Adj e)={z} := by
      ext x
      constructor
      · intro xm
        obtain ⟨m,ex⟩ := mem_filter.mp xm
        have nb := (G.mem_neighborFinset ..).mpr ex
        rw [n,mem_insert,mem_singleton] at nb
        rcases nb with rfl|rfl
        · rcases mem_union.mp m with a|b
          · exact (G.not_mem_neighborFinset_self _ (mem_inter.mp a).1).elim
          · exact ((mem_sdiff.mp (MB b)).2 v.property).elim
        · exact mem_singleton_self _
      · intro hm
        have xz := mem_singleton.mp hm
        subst x
        exact mem_filter.mpr ⟨mem_union_left _ za,ez⟩
    unfold nbr
    rw [cnt,card_singleton]
  have add : ∀ S⊆B,(pairs G (A∪S)).card=(pairs G A).card+S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert e S out ih =>
      intro es
      have em := es (mem_insert_self ..)
      have ss : S⊆B := (subset_insert _ _).trans es
      have ea : e∉A := fun h=>(mem_sdiff.mp em).2 (mem_inter.mp h).2
      have eoff : e∉A∪S := fun m=>(mem_union.mp m).elim ea out
      have un : A∪insert e S=insert e (A∪S) := by
        ext x; simp [or_left_comm]
      rw [un,pairs_insert G eoff,aj e em _ ss,ih ss,card_insert_of_not_mem out]
      omega
  let f : H ↪ V := Function.Embedding.subtype _
  have equiv : (pairs J (J.neighborFinset v)).image (fun p=>p.map f)=pairs G A := by
    ext p
    constructor
    · intro pm
      obtain ⟨q,qm,rfl⟩ := mem_image.mp pm
      obtain ⟨x,xm,y,ym,xy,rfl⟩ := (pair_mem J).mp qm
      have ax : x.val∈A := mem_inter.mpr
        ⟨(G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp xm),x.property⟩
      have ay : y.val∈A := mem_inter.mpr
        ⟨(G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp ym),y.property⟩
      apply (pair_mem G).mpr
      exact ⟨x.val,ax,y.val,ay,xy,by simp [f]⟩
    · intro pm
      obtain ⟨x,xm,y,ym,xy,rfl⟩ := (pair_mem G).mp pm
      let vx : H := ⟨x,(mem_inter.mp xm).2⟩
      let vy : H := ⟨y,(mem_inter.mp ym).2⟩
      have jx : vx∈J.neighborFinset v :=
        (J.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp (mem_inter.mp xm).1)
      have jy : vy∈J.neighborFinset v :=
        (J.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp (mem_inter.mp ym).1)
      exact mem_image.mpr ⟨{vx,vy},(pair_mem J).mpr ⟨vx,jx,vy,jy,xy,rfl⟩,by simp [f,vx,vy]⟩
  have high : trianglesAt J v=(pairs G A).card := by
    rw [←equiv,card_image_of_injective _ (Finset.map_injective f)]
    rfl
  have low : B.card=nbr G v.val Hᶜ := by
    unfold B nbr
    congr 1
    ext x
    simp [N,and_comm]
  change (pairs G N).card=trianglesAt J v+nbr G v.val Hᶜ
  rw [←AB,add B Subset.rfl,high,low]

#print axioms triangle_count_high_with_independent_ears
end Graffiti384b.DiversityEleven
