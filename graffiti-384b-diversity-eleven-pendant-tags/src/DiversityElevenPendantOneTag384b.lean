import DiversityElevenPendantBoard384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- In an eight-vertex board of minimum degree three, any prescribed
vertex extends to a dominating triple. After retaining it there are
at most four uncovered vertices; each forbids at most three out of
the 21 pairs from the remaining seven vertices. -/
theorem dominating_triple_of_eight (B : Finset V) (size : B.card=8)
    (dense : ∀ v∈B, 3≤nbr G v B) {p : V} (pm : p∈B) :
    ∃ K⊆B, K.card=3 ∧ p∈K ∧
      ∀ v∈B \ K, 0<nbr G v K := by
  classical
  let T := B.erase p
  let M := T.filter (fun v => ¬G.Adj p v)
  let bad (v : V) := ((T.erase v).filter (fun w => ¬G.Adj v w)).powersetCard 2
  let all := T.powersetCard 2
  have Ts : T.card=7 := by dsimp [T]; rw [card_erase_of_mem pm,size]
  have Ms : M.card≤4 := by
    have same : T.filter (G.Adj p)=B.filter (G.Adj p) := by
      ext w; simp only [T,mem_filter,mem_erase]
      exact ⟨fun h=>⟨h.1.2,h.2⟩,fun h=>⟨⟨h.2.ne.symm,h.1⟩,h.2⟩⟩
    have d : 3≤(B.filter (G.Adj p)).card := dense p pm
    have s := filter_card_add_filter_neg_card_eq_card (s:=T) (G.Adj p)
    rw [same,Ts] at s
    change _+M.card=7 at s
    omega
  have few (v : V) (vm : v∈M) : (bad v).card≤3 := by
    have vt : v∈T := (mem_filter.mp vm).1
    have vp : ¬G.Adj v p := fun h => (mem_filter.mp vm).2 h.symm
    have ne : (T.erase v).filter (G.Adj v)=B.filter (G.Adj v) := by
      ext w; simp only [T,mem_filter,mem_erase]
      exact ⟨fun h=>⟨h.1.2.2,h.2⟩,fun h=>⟨⟨h.2.ne.symm,⟨fun e => vp (e ▸ h.2),h.1⟩⟩,h.2⟩⟩
    have d : 3≤(B.filter (G.Adj v)).card := dense v (mem_erase.mp vt).2
    have s := filter_card_add_filter_neg_card_eq_card (s:=T.erase v) (G.Adj v)
    rw [ne,card_erase_of_mem vt,Ts] at s
    have atmost : ((T.erase v).filter (fun w => ¬G.Adj v w)).card≤3 := by omega
    change _≤3
    dsimp [bad]
    rw [card_powersetCard]
    exact (Nat.choose_le_choose 2 atmost).trans (by decide)
  have cap : (M.biUnion bad).card≤12 := by
    calc
      _ ≤ ∑ v∈M,(bad v).card := card_biUnion_le
      _ ≤ ∑ _v∈M,3 := sum_le_sum few
      _ ≤ 12 := by simpa [sum_const] using Nat.mul_le_mul_right 3 Ms
  have allsize : all.card=21 := by dsimp [all]; rw [card_powersetCard,Ts]; decide
  have ex : (all \ M.biUnion bad).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro empty
    have cardinal := card_le_card (sdiff_eq_empty_iff_subset.mp empty)
    rw [allsize] at cardinal
    omega
  obtain ⟨R,rm⟩ := ex
  obtain ⟨ra,rnb⟩ := mem_sdiff.mp rm
  obtain ⟨rs,r2⟩ := mem_powersetCard.mp ra
  have pR : p∉R := fun h => (mem_erase.mp (rs h)).1 rfl
  let K := insert p R
  have ks : K⊆B := insert_subset pm (rs.trans (erase_subset ..))
  have k3 : K.card=3 := by dsimp [K]; rw [card_insert_of_not_mem pR,r2]
  refine ⟨K,ks,k3,mem_insert_self ..,?_⟩
  intro v vm
  obtain ⟨vB,vK⟩ := mem_sdiff.mp vm
  have vp : v≠p := fun h => vK (h ▸ mem_insert_self ..)
  have vn : v∉R := fun h => vK (mem_insert_of_mem h)
  by_cases hz : 0<nbr G v K
  · exact hz
  exfalso
  have notadj {w : V} (wK : w∈K) : ¬G.Adj v w := by
    intro vw
    have pos : 0<nbr G v K := card_pos.mpr ⟨w,mem_filter.mpr ⟨wK,vw⟩⟩
    omega
  have mz : v∈M := mem_filter.mpr ⟨mem_erase.mpr ⟨vp,vB⟩,
    fun pv => notadj (mem_insert_self ..) pv.symm⟩
  apply rnb (mem_biUnion.mpr ⟨v,mz,?_⟩)
  apply mem_powersetCard.mpr
  refine ⟨?_,r2⟩
  intro w wm
  refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_,rs wm⟩,notadj (mem_insert_of_mem wm)⟩
  exact fun h => vn (h ▸ wm)

theorem exact_pendant_at_most_one_tag (t : (types G).card=11) (nine : (high G).card=9)
    {e f a : V} (ea : G.Adj e a) (ef : G.Adj e f) (ah : a∈high G)
    (el : e∉high G) (fl : f∉high G)
    (dense : ∀ v∈(high G).erase a,3≤nbr G v ((high G).erase a))
    (tags : (((high G).erase a).filter (fun v => ¬G.Adj v a)).card≤1) :
    gamma G≤bound G := by
  classical
  let B := (high G).erase a
  let Z := B.filter (fun v => ¬G.Adj v a)
  have s : B.card=8 := by dsimp [B]; rw [card_erase_of_mem ah,nine]
  obtain ⟨p,pB,covers⟩ : ∃ p∈B,∀ v∈Z,v=p := by
    by_cases non : Z.Nonempty
    · obtain ⟨p,pm⟩ := non
      refine ⟨p,(mem_filter.mp pm).1,?_⟩
      intro v vm
      exact (card_le_one.mp tags) _ vm _ pm
    · obtain ⟨p,pm⟩ := card_pos.mp (show 0<B.card by rw [s]; decide)
      exact ⟨p,pm,fun v vm => (non ⟨v,vm⟩).elim⟩
  obtain ⟨K,ks,k3,pk,good⟩ := dominating_triple_of_eight G B s dense pB
  refine exact_of_pendant_triple G t nine ea ef ah el fl ks k3 (fun v vm => ?_)
  have va : G.Adj v a := by
    by_cases va : G.Adj v a
    · exact va
    exfalso
    have ve := covers v (mem_filter.mpr ⟨(mem_sdiff.mp vm).1,va⟩)
    exact (mem_sdiff.mp vm).2 (ve ▸ pk)
  have hh := good v vm
  rw [if_pos va]
  omega

#print axioms dominating_triple_of_eight
#print axioms exact_pendant_at_most_one_tag
end Graffiti384b.DiversityEleven
