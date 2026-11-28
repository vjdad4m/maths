import DiversityElevenOneCenter384b
import DiversityElevenPendantSplit384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Graffiti384b.DiversityEleven.cubic_pair_nonadjacent from ThreeUntouched384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact dense pendant conclusion holds with at most two vertices
missing the high anchor. If there are two, retain both; their cubic
adjacency restriction leaves at most three unresolved vertices in the
six-vertex remainder, which admits one more universal covering choice. -/
theorem exact_pendant_at_most_two_tags (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) {e f a : V} (ah : a∈high G)
    (low : nonleaves G \ high G={e,f}) (en : G.neighborFinset e={f,a})
    (fn : G.neighborFinset f={e,a})
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v)
    (dense : ∀ v∈(high G).erase a, 3≤nbr G v ((high G).erase a))
    (tags : (((high G).erase a).filter (fun v => ¬G.Adj v a)).card≤2) :
    gamma G≤bound G := by
  classical
  let B := (high G).erase a
  let Z := B.filter (fun v => ¬G.Adj v a)
  have s : B.card=8 := by dsimp [B]; rw [card_erase_of_mem ah,nine]
  have el : e∉high G := (mem_sdiff.mp (low ▸ mem_insert_self _ _)).2
  have fl : f∉high G := (mem_sdiff.mp (low ▸ mem_insert_of_mem (mem_singleton_self _))).2
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have ef : G.Adj e f := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self _ _)
  by_cases z1 : Z.card≤1
  · exact exact_pendant_at_most_one_tag G t nine ea ef ah el fl dense z1
  have z2 : Z.card=2 := by change Z.card≤2 at tags; omega
  obtain ⟨p,q,pq,zpq⟩ := card_eq_two.mp z2
  have pm : p∈Z := zpq ▸ mem_insert_self _ _
  have qm : q∈Z := zpq ▸ mem_insert_of_mem (mem_singleton_self _)
  have pB : p∈B := (mem_filter.mp pm).1
  have qB : q∈B := (mem_filter.mp qm).1
  let T := B\Z
  let M := T.filter (fun v => ¬G.Adj v p ∧ ¬G.Adj v q)
  have zsub : Z⊆B := filter_subset _ _
  have Ts : T.card=6 := by dsimp [T]; rw [card_sdiff zsub,s,z2]
  have msub : M⊆T := filter_subset _ _
  have mB : M⊆B := msub.trans sdiff_subset
  have mc : M.card≤3 := by
    by_contra! large
    let R := B\M
    have cap : R.card≤4 := by dsimp [R]; rw [card_sdiff mB,s]; omega
    have loc {v : V} (vm : v∈Z) :
        B.filter (G.Adj v) = R.erase v ∧ G.degree v=3 := by
      have vR : v∈R := mem_sdiff.mpr ⟨zsub vm,fun h => (mem_sdiff.mp (msub h)).2 vm⟩
      have sub : B.filter (G.Adj v)⊆R.erase v := by
        intro w wm
        obtain ⟨wB,vw⟩ := mem_filter.mp wm
        apply mem_erase.mpr ⟨vw.ne.symm,mem_sdiff.mpr ⟨wB,?_⟩⟩
        intro wM
        have pair : v=p ∨ v=q := by simpa [zpq] using vm
        rcases pair with rfl|rfl
        · exact (mem_filter.mp wM).2.1 vw.symm
        · exact (mem_filter.mp wM).2.2 vw.symm
      have up := card_le_card sub
      rw [card_erase_of_mem vR] at up
      have down : 3≤(B.filter (G.Adj v)).card := dense v (zsub vm)
      have eq : B.filter (G.Adj v)=R.erase v := eq_of_subset_of_card_le sub (by
        rw [card_erase_of_mem vR]; omega)
      have d := (pendant_board_local G sup ah low en fn (zsub vm)).2
      change (B.filter (G.Adj v)).card + _ = _ at d
      rw [if_neg (mem_filter.mp vm).2] at d
      exact ⟨eq,by omega⟩
    have hp := loc pm
    have hq := loc qm
    have qR : q∈R := mem_sdiff.mpr ⟨qB,fun h => (mem_sdiff.mp (msub h)).2 qm⟩
    have edge : G.Adj p q := (mem_filter.mp (hp.1.symm ▸ mem_erase.mpr ⟨pq.symm,qR⟩)).2
    have ph := (mem_erase.mp pB).2
    have qh := (mem_erase.mp qB).2
    have d : trianglesAt G p≠trianglesAt G q := fun eq => pq (scores ph qh eq)
    exact Graffiti384b.DiversityEleven.cubic_pair_nonadjacent G hp.2 hq.2 (mins _ ph) (mins _ qh) d edge
  have md : ∀ v∈M, 3≤nbr G v T := by
    intro v vm
    have eq : T.filter (G.Adj v)=B.filter (G.Adj v) := by
      ext w
      simp only [T,mem_filter,mem_sdiff]
      refine ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,?_⟩,h.2⟩⟩
      intro z
      have z' : w=p ∨ w=q := by simpa [zpq] using z
      rcases z' with rfl|rfl
      · exact (mem_filter.mp vm).2.1 h.2
      · exact (mem_filter.mp vm).2.2 h.2
    change 3≤(T.filter (G.Adj v)).card
    rw [eq]
    exact dense v (mB vm)
  obtain ⟨b,bt,bg⟩ := one_center_of_six G T M Ts msub mc md
  let K := insert b Z
  have Ksub : K⊆B := insert_subset (mem_sdiff.mp bt).1 zsub
  have Ksz : K.card=3 := by dsimp [K]; rw [card_insert_of_not_mem (mem_sdiff.mp bt).2,z2]
  apply exact_of_pendant_triple G t nine ea ef ah el fl Ksub Ksz
  intro v vm
  obtain ⟨vB,vK⟩ := mem_sdiff.mp vm
  have vz : v∉Z := fun h => vK (mem_insert_of_mem h)
  have va : G.Adj v a := by
    by_cases adj : G.Adj v a
    · exact adj
    exfalso
    exact vz (mem_filter.mpr ⟨vB,adj⟩)
  rw [if_pos va]
  have witness : ∃ x∈K,G.Adj v x := by
    by_cases vp : G.Adj v p
    · exact ⟨p,mem_insert_of_mem pm,vp⟩
    by_cases vq : G.Adj v q
    · exact ⟨q,mem_insert_of_mem qm,vq⟩
    have vM : v∈M := mem_filter.mpr ⟨mem_sdiff.mpr ⟨vB,vz⟩,vp,vq⟩
    rcases bg v vM with eq|ed
    · exact (vK (eq ▸ mem_insert_self ..)).elim
    · exact ⟨b,mem_insert_self ..,ed⟩
  obtain ⟨x,xk,vx⟩ := witness
  have n : 0<nbr G v K := card_pos.mpr ⟨x,mem_filter.mpr ⟨xk,vx⟩⟩
  omega

#print axioms exact_pendant_at_most_two_tags
end Graffiti384b.DiversityEleven
