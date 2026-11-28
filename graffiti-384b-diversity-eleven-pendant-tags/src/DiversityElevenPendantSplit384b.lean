import DiversityElevenPendantCubic384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Graffiti384b.DiversityEleven.cubic_pair_nonadjacent from ThreeUntouched384b
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A disconnected order-eight dense pendant board must split into two
four-cliques. Each clique has at most one vertex missing the anchor,
since adjacent ambient cubic vertices cannot have distinct rich scores.
Keeping one vertex per clique therefore suffices. -/
theorem exact_of_pendant_board_split (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) {e f a : V} (ah : a∈high G)
    (low : nonleaves G \ high G={e,f}) (en : G.neighborFinset e={f,a})
    (fn : G.neighborFinset f={e,a})
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v)
    (dense : ∀ v∈(high G).erase a, 3≤nbr G v ((high G).erase a))
    {X Y : Finset V} (xn : X.Nonempty) (yn : Y.Nonempty)
    (dis : Disjoint X Y) (cover : X∪Y=(high G).erase a)
    (anti : ∀ x∈X, ∀ y∈Y, ¬G.Adj x y) : gamma G≤bound G := by
  classical
  let B := (high G).erase a
  have xB : X ⊆ B := fun v vm => (show v∈(high G).erase a from cover ▸ mem_union_left _ vm)
  have yB : Y ⊆ B := fun v vm => (show v∈(high G).erase a from cover ▸ mem_union_right _ vm)
  have size : X.card+Y.card=8 := by
    rw [←card_union_of_disjoint dis,cover,card_erase_of_mem ah,nine]
  have link {S T : Finset V} (eq : S∪T=B)
      (no : ∀ x∈S,∀ y∈T,¬G.Adj x y) {v : V} (vS : v∈S) :
      B.filter (G.Adj v) ⊆ S.erase v := by
    intro w wm
    obtain ⟨wB,vw⟩ := mem_filter.mp wm
    have h : w∈S∪T := eq.symm ▸ wB
    exact mem_erase.mpr ⟨vw.ne.symm,(mem_union.mp h).resolve_right (fun wt => no v vS w wt vw)⟩
  have anti' : ∀ y∈Y,∀ x∈X,¬G.Adj y x := fun y ym x xm a => anti x xm y ym a.symm
  have rev : Y∪X=B := (union_comm ..).trans cover
  have lower {S T : Finset V} (eq : S∪T=B)
      (sub : S⊆B) (no : ∀ x∈S,∀ y∈T,¬G.Adj x y) (ne : S.Nonempty) : 4≤S.card := by
    obtain ⟨v,vm⟩ := ne
    have l := card_le_card (link eq no vm)
    rw [card_erase_of_mem vm] at l
    have d : 3≤(B.filter (G.Adj v)).card := dense v (sub vm)
    omega
  have sx : X.card=4 := by have l := lower cover xB anti xn; have m := lower rev yB anti' yn; omega
  have sy : Y.card=4 := by omega
  have feat {S T : Finset V} (eq : S∪T=B) (sub : S⊆B) (s : S.card=4)
      (no : ∀ x∈S,∀ y∈T,¬G.Adj x y) {v : V} (vS : v∈S) :
      B.filter (G.Adj v)=S.erase v := by
    have l := link eq no vS
    apply eq_of_subset_of_card_le l
    have d : 3≤(B.filter (G.Adj v)).card := dense v (sub vS)
    rw [card_erase_of_mem vS,s]
    omega
  have pick {S T : Finset V} (eq : S∪T=B) (sub : S⊆B) (s : S.card=4)
      (no : ∀ x∈S,∀ y∈T,¬G.Adj x y) (ne : S.Nonempty) :
      ∃ p∈S, ∀ v∈S, v≠p → G.Adj v p ∧ G.Adj v a := by
    have f (v : V) (vS : v∈S) := feat eq sub s no vS
    have clique {v w : V} (vS : v∈S) (wS : w∈S) (vw : v≠w) : G.Adj v w :=
      (mem_filter.mp ((f v vS).symm ▸ mem_erase.mpr ⟨vw.symm,wS⟩)).2
    have deg {v : V} (vS : v∈S) (va : ¬G.Adj v a) : G.degree v=3 := by
      have d := (pendant_board_local G sup ah low en fn (sub vS)).2
      change (B.filter (G.Adj v)).card + (if G.Adj v a then 1 else 0) = G.degree v at d
      rw [f v vS,card_erase_of_mem vS,s,if_neg va] at d
      omega
    by_cases ex : ∃ p∈S, ¬G.Adj p a
    · obtain ⟨p,pm,pa⟩ := ex
      refine ⟨p,pm,fun v vm vp => ⟨clique vm pm vp,?_⟩⟩
      by_cases va : G.Adj v a
      · exact va
      exfalso
      have vh := (mem_erase.mp (sub vm)).2
      have ph := (mem_erase.mp (sub pm)).2
      have d : trianglesAt G v≠trianglesAt G p := fun h => vp (scores vh ph h)
      exact Graffiti384b.DiversityEleven.cubic_pair_nonadjacent G (deg vm va) (deg pm pa)
        (mins _ vh) (mins _ ph) d (clique vm pm vp)
    · obtain ⟨p,pm⟩ := ne
      refine ⟨p,pm,fun v vm vp => ⟨clique vm pm vp,?_⟩⟩
      by_cases va : G.Adj v a
      · exact va
      exfalso
      exact ex ⟨v,vm,va⟩
  obtain ⟨p,px,src⟩ := pick cover xB sx anti xn
  obtain ⟨q,qy,dst⟩ := pick rev yB sy anti' yn
  have pq : p≠q := fun h => disjoint_left.mp dis px (h ▸ qy)
  let K0 : Finset V := {p,q}
  have ksub : K0⊆B := insert_subset (xB px) (singleton_subset_iff.mpr (yB qy))
  have ksz : K0.card=2 := card_pair pq
  have Bsz : B.card=8 := by dsimp [B]; rw [card_erase_of_mem ah,nine]
  obtain ⟨b,bm⟩ := card_pos.mp (show 0<(B\K0).card by rw [card_sdiff ksub,Bsz,ksz]; decide)
  let K := insert b K0
  have Ksub : K⊆B := insert_subset (mem_sdiff.mp bm).1 ksub
  have Ksz : K.card=3 := by dsimp [K]; rw [card_insert_of_not_mem (mem_sdiff.mp bm).2,ksz]
  have el : e∉high G := (mem_sdiff.mp (low ▸ mem_insert_self _ _)).2
  have fl : f∉high G := (mem_sdiff.mp (low ▸ mem_insert_of_mem (mem_singleton_self _))).2
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have ef : G.Adj e f := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self _ _)
  apply exact_of_pendant_triple G t nine ea ef ah el fl Ksub Ksz
  intro v vm
  obtain ⟨vB,vK⟩ := mem_sdiff.mp vm
  have pc : p∈K := mem_insert_of_mem (mem_insert_self _ _)
  have qc : q∈K := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have h (x : V) (xK : x∈K) (vx : G.Adj v x ∧ G.Adj v a) :
      2≤nbr G v K+(if G.Adj v a then 1 else 0) := by
    rw [if_pos vx.2]
    have p : 0<nbr G v K := card_pos.mpr ⟨x,mem_filter.mpr ⟨xK,vx.1⟩⟩
    omega
  have hv : v∈X∪Y := cover.symm ▸ vB
  rcases mem_union.mp hv with vx|vy
  · exact h _ pc (src v vx (fun he => vK (he ▸ pc)))
  · exact h _ qc (dst v vy (fun he => vK (he ▸ qc)))

#print axioms exact_of_pendant_board_split
end Graffiti384b.DiversityEleven
