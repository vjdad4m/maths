import DiversityElevenExactThreeSelector384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph ShorePairs
open private Graffiti384b.DiversityEleven.triangle_range_eight Graffiti384b.DiversityEleven.count_eight from DiversityElevenPendantFinite384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def EightSelectorAt (k : Nat) : Prop :=
  ∀ (H : SimpleGraph (Fin 8)) (dec : DecidableRel H.Adj) (Z : Finset (Fin 8)),
    letI := dec
    (∀ i,3≤H.degree i) → Z.card=k →
    (∀ i∈Z,2≤trianglesAt H i) → Set.InjOn (trianglesAt H) (Z : Set (Fin 8)) →
    ∃ K : Finset (Fin 8), K.card=3 ∧ ∀ i∉K,
      (if i∈Z then 2 else 1)≤nbr H i K

theorem exact_pendant_selector_at {k : Nat} (select : EightSelectorAt k)
    (sup : Supported G) (t : (types G).card=11) (nine : (high G).card=9)
    {e f a : V} (ah : a∈high G) (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a})
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v)
    (dense : ∀ v∈(high G).erase a, 3≤nbr G v ((high G).erase a))
    (tagcount : (((high G).erase a).filter (fun v => ¬G.Adj v a)).card=k) :
    gamma G≤bound G := by
  classical
  let B := (high G).erase a
  let U := B.filter (fun v => ¬G.Adj v a)
  have sz : B.card=8 := by dsimp [B]; rw [card_erase_of_mem ah,nine]
  let l : Fin 8 ≃ B := (Fintype.equivFinOfCardEq
    (show Fintype.card B=8 by rwa [Fintype.card_coe])).symm
  let H := G.comap (fun i => (l i).val)
  let dec : DecidableRel H.Adj := fun i j => inferInstanceAs (Decidable (G.Adj (l i).val (l j).val))
  letI := dec
  let F : Fin 8 ↪ V := l.toEmbedding.trans (Function.Embedding.subtype _)
  let Z := univ.filter (fun i : Fin 8 => ¬G.Adj (l i).val a)
  have tag (i : Fin 8) : i∈Z ↔ ¬G.Adj (l i).val a := by simp [Z]
  have eq : Z.map F=U := by
    ext v
    constructor
    · intro vm
      obtain ⟨i,iz,rfl⟩ := mem_map.mp vm
      exact mem_filter.mpr ⟨(l i).property,(tag i).mp iz⟩
    · intro vm
      obtain ⟨vB,va⟩ := mem_filter.mp vm
      let i := l.symm ⟨v,vB⟩
      have iv : (l i).val=v := by simp [i]
      exact mem_map.mpr ⟨i,(tag i).mpr (by rwa [iv]),iv⟩
  have UZ : U.card=Z.card := by rw [←eq,card_map]
  have zc : Z.card=k := UZ.symm.trans tagcount
  have de (i : Fin 8) : 3≤H.degree i := by
    rw [Graffiti384b.DiversityEleven.count_eight G B l i]
    exact dense _ (l i).property
  have ht (i : Fin 8) (iz : i∈Z) : trianglesAt H i=trianglesAt G (l i).val := by
    apply Graffiti384b.DiversityEleven.triangle_range_eight G B l i
    intro x y ix iy _
    have hn := (pendant_board_local G sup ah low en fn (l i).property).1
    have sub {u : V} (iu : G.Adj (l i).val u) : u∈B :=
      mem_erase.mpr ⟨fun e => (tag i).mp iz (e ▸ iu),hn u iu⟩
    exact ⟨sub ix,sub iy⟩
  have hh (i : Fin 8) : (l i).val∈high G := (mem_erase.mp (l i).property).2
  have sc : Set.InjOn (trianglesAt H) (Z : Set (Fin 8)) := by
    intro i ih j jh he
    apply l.injective
    apply Subtype.ext
    exact scores (hh i) (hh j) ((ht i ih).symm.trans (he.trans (ht j jh)))
  obtain ⟨K,k3,good⟩ := select H dec Z de zc
    (fun i iz => (ht i iz).symm ▸ mins _ (hh i)) sc
  let M := K.map F
  have ms : M⊆B := by
    intro v vm
    obtain ⟨i,_,rfl⟩ := mem_map.mp vm
    exact (l i).property
  have m3 : M.card=3 := (card_map ..).trans k3
  have el : e∉high G := (mem_sdiff.mp (low ▸ mem_insert_self _ _)).2
  have fl : f∉high G := (mem_sdiff.mp (low ▸ mem_insert_of_mem (mem_singleton_self _))).2
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have ef : G.Adj e f := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self _ _)
  apply exact_of_pendant_triple G t nine ea ef ah el fl ms m3
  intro v vm
  obtain ⟨vB,vM⟩ := mem_sdiff.mp vm
  let i := l.symm ⟨v,vB⟩
  have iv : (l i).val=v := by simp [i]
  have ik : i∉K := fun h => vM (mem_map.mpr ⟨i,h,iv⟩)
  have ce : (K.filter (H.Adj i)).map F=M.filter (G.Adj v) := by
    ext w
    constructor
    · intro hw
      obtain ⟨j,jm,rfl⟩ := mem_map.mp hw
      exact mem_filter.mpr ⟨mem_map.mpr ⟨j,(mem_filter.mp jm).1,rfl⟩,
        by rw [←iv]; exact (mem_filter.mp jm).2⟩
    · intro hw
      obtain ⟨wm,vw⟩ := mem_filter.mp hw
      obtain ⟨j,jm,rfl⟩ := mem_map.mp wm
      exact mem_map.mpr ⟨j,mem_filter.mpr ⟨jm,by change G.Adj (l i).val _; rwa [iv]⟩,rfl⟩
  have cnt : nbr H i K=nbr G v M := (card_map ..).symm.trans (congrArg card ce)
  have g := good i ik
  rw [cnt] at g
  have z : i∈Z ↔ ¬G.Adj v a := (tag i).trans (by rw [iv])
  by_cases va : G.Adj v a
  · rw [if_neg (fun h => (z.mp h) va)] at g
    rw [if_pos va]
    omega
  · rw [if_pos (z.mpr va)] at g
    simpa [va] using g

/-- Exact closure for an arbitrary supported pendant graph with three
high vertices missing the anchor, not merely a labelled graph model. -/
theorem exact_pendant_three_tags (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) {e f a : V} (ah : a∈high G)
    (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a})
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v)
    (dense : ∀ v∈(high G).erase a, 3≤nbr G v ((high G).erase a))
    (tags : (((high G).erase a).filter (fun v => ¬G.Adj v a)).card=3) :
    gamma G≤bound G :=
  exact_pendant_selector_at G (fun H dec Z dg zc mn sc =>
    letI := dec
    exact_three_selector H Z zc dg mn sc) sup t nine ah low en fn scores mins dense tags

#print axioms exact_pendant_selector_at
#print axioms exact_pendant_three_tags
end Graffiti384b.DiversityEleven
