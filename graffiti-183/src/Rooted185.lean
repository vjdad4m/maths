import OrderBridge

namespace Graffiti179
open Finset SimpleGraph Short177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]
theorem complete_state_rooted (hc : G.Connected)
    (localTrim : ∀ (pool : Finset V) (x : V) (b : Block G pool {x}),
      Nonempty (Trim G pool (b.A ∪ b.B) x))
    (gain : ℕ) (S D : Finset V) (st : State G gain S D) (hs : S.Nonempty) (root : V) (hr : root ∈ D) (hrS : root ∈ S) :
    ∃ E B : Finset V, root ∈ E ∧ root ∈ B ∧ Graffiti177.Con G E ∧
      closed G E = univ ∧ TwoColor G B ∧ E.card + gain ≤ B.card := by
  classical
  by_cases full : closed G S = univ
  · exact ⟨D,S,hr,hrS,st.conn,subset_antisymm (subset_univ _) (full ▸ st.dom),st.bip,st.budget⟩
  obtain ⟨c,cs,x,xs,cx⟩ := connector G hc hs full
  let pool := univ \ closed G S
  have seed : ({x} : Finset V) ⊆ pool := by simp [pool,xs]
  have col : TwoColor G {x} := by
    refine ⟨{x},∅,by simp,by simp,?_,?_⟩ <;> simp [Indep]
  obtain ⟨b⟩ := exists_block G seed (Graffiti177.con_single G x) col
  obtain ⟨trim⟩ := localTrim pool x b
  let T := b.A ∪ b.B
  have xt : x ∈ T := b.seeded (mem_singleton_self _)
  have sep : ∀ v ∈ T, v ∉ closed G S := fun v hv => (mem_sdiff.mp (b.inside hv)).2
  have bi : TwoColor G T := ⟨b.A,b.B,b.disjoint,rfl,b.indA,b.indB⟩
  have coverage : ∀ z ∈ closed G T, z ∈ closed G S ∨ z = x ∨ z ∈ closed G trim.keep := by
    intro z hz
    have h := trim.covers z hz
    simpa [pool] using h
  have grown := PreparedStep G st bi sep cs cx trim.size trim.connected coverage
  have sub : S ⊂ S ∪ T := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left,?_⟩
    intro eq
    exact xs ((mem_closed G).mpr (Or.inl (eq.symm ▸ (mem_union_right S xt))))
  have lt := card_lt_card sub
  have le := card_le_univ (s := S ∪ T)
  exact complete_state_rooted hc localTrim gain (S ∪ T) (insert c D ∪ trim.keep) grown
    ⟨x,mem_union_right S xt⟩ root (mem_union_left _ (mem_insert_of_mem hr)) (mem_union_left _ hrS)
termination_by Fintype.card V - S.card
decreasing_by
  change Fintype.card V - (S ∪ T).card < Fintype.card V - S.card
  omega

theorem rooted_dom (hc : G.Connected) (hn : 1 < Fintype.card V) (x : V) :
    ∃ E B : Finset V, x ∈ E ∧ x ∈ B ∧ Graffiti177.Con G E ∧
      closed G E = univ ∧ TwoColor G B ∧ E.card + 1 ≤ B.card := by
  classical
  obtain ⟨y,xy⟩ := Graffiti177.exists_adj G hc hn x
  let U : Finset V := {x,y}
  have co : Graffiti177.Con G U := Graffiti177.con_insert G (Graffiti177.con_single G y) (by simp) xy
  have col : TwoColor G U := by
    refine ⟨{x},{y},by simp [xy.ne.symm],by ext q; simp [U],?_,?_⟩ <;> simp [Indep]
  obtain ⟨b⟩ := exists_block G (subset_univ U) co col
  let b' : Block G univ {x} :=
    ⟨b.A,b.B,b.disjoint,b.indA,b.indB,b.conn,b.inside,
      (singleton_subset_iff.mpr (show x ∈ U from by simp [U])).trans b.seeded,b.maximal⟩
  let T := b'.A ∪ b'.B
  have u2 : 2 ≤ T.card :=
    (card_pair xy.ne).symm.le.trans (card_le_card b.seeded)
  obtain ⟨t,kt⟩ := trim_one_preserves_seed G univ x b'
  have xk := kt u2
  have con : Graffiti177.Con G t.keep := by
    rcases t.connected with e | ⟨c,_⟩
    · rw [e] at xk
      exact (not_mem_empty _ xk).elim
    · exact c
  have dom : closed G T ⊆ closed G t.keep := by
    intro z hz
    rcases t.covers z hz with bad | rfl | hh
    · exact (bad (mem_univ _)).elim
    · exact (mem_closed G).mpr (Or.inl xk)
    · exact hh
  have blank : State G 1 T t.keep :=
    ⟨⟨b'.A,b'.B,b'.disjoint,rfl,b'.indA,b'.indB⟩,con,t.size,dom⟩
  exact complete_state_rooted G hc (trim_one G) 1 T t.keep blank
    ⟨x,b'.seeded (mem_singleton_self _)⟩ x xk (b'.seeded (mem_singleton_self _))


#print axioms rooted_dom
end Graffiti179
