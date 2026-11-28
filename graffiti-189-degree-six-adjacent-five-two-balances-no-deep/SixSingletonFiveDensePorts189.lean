import SixSingletonFiveDenseBalances189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private d8 k3 finish_by_balance from SixSingletonFiveShallowRoute189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem small_common_path
    (cover : ∀ c∈K,∃ t∈K,G.Adj c t) : ∃ c∈K,∃ t∈K,RouteOn G K c t := by
  by_cases h : G.Adj 5 6
  · by_cases j : G.Adj 5 7
    · exact ⟨6,by decide,7,by decide,by
        simpa only [show ({6,5,7} : Finset V)=K by decide] using RouteOn.three h.symm j (by decide)⟩
    obtain ⟨t,m,e⟩ := cover 7 (by decide)
    have shape : ∀ x∈K,x=5 ∨ x=6 ∨ x=7 := by decide
    rcases shape t m with e'|e'|e'
    · subst t; exact (j e.symm).elim
    · subst t
      exact ⟨5,by decide,7,by decide,by
        simpa only [show ({5,6,7} : Finset V)=K by decide] using RouteOn.three h e.symm (by decide)⟩
    · exact (e.ne e'.symm).elim
  have shape : ∀ x∈K,x=5 ∨ x=6 ∨ x=7 := by decide
  obtain ⟨u,um,hu⟩ := cover 5 (by decide)
  obtain ⟨t,tm,ht⟩ := cover 6 (by decide)
  have u7 : u=7 := (shape u um).resolve_left (fun q=>hu.ne q.symm) |>.resolve_left (fun q=>h (q ▸ hu))
  have t7 : t=7 := (shape t tm).resolve_left (fun q=>h (q ▸ ht.symm)) |>.resolve_left (fun q=>ht.ne q.symm)
  subst u t
  exact ⟨5,by decide,6,by decide,by
    simpa only [show ({5,7,6} : Finset V)=K by decide] using RouteOn.three hu ht.symm (by decide)⟩

private theorem common_exit_balance (W : Finset V) (w2 : W.card=2)
    (high : ∀ c∈K,6≤G.degree c)
    (bound : ∀ c∈K,∀ t,G.Adj c t → t∈insert a (insert b (P∪W)))
    (noBoth : ∀ c∈K,¬(G.Adj c x ∧ G.Adj c y)) :
    ∃ c∈K,∃ t∈K,∃ z∈W,RouteOn G K c t ∧ G.Adj z c := by
  classical
  have scope (c : V) (cm : c∈K) :
      G.neighborFinset c⊆insert a (insert b (insert (if G.Adj c x then x else y) ((K.erase c)∪W))) := by
    intro z zm
    have cz := (mem_neighborFinset _ _ _).mp zm
    rcases mem_insert.mp (bound c cm z cz) with q|q
    · exact mem_insert.mpr (.inl q)
    rcases mem_insert.mp q with q|q
    · exact mem_insert_of_mem (mem_insert.mpr (.inl q))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    rcases mem_union.mp q with q|q
    · rcases mem_insert.mp q with p|p
      · exact mem_insert.mpr (.inl (p.trans (if_pos (p ▸ cz)).symm))
      rcases mem_insert.mp p with p|p
      · have n : ¬G.Adj c x := fun e=>noBoth c cm ⟨e,p ▸ cz⟩
        exact mem_insert.mpr (.inl (p.trans (if_neg n).symm))
      exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨cz.ne.symm,p⟩))
    exact mem_insert_of_mem (mem_union_right _ q)
  have balance (c : V) (cm : c∈K) : ∃ z∈W,G.Adj z c := by
    by_contra no
    have ss : G.neighborFinset c⊆insert a (insert b (insert (if G.Adj c x then x else y) (K.erase c))) := by
      intro z zm
      have n := scope c cm zm
      simp only [mem_insert,mem_union] at n ⊢
      exact n.elim Or.inl (fun e=>Or.inr (e.elim Or.inl (fun e=>Or.inr
        (e.elim Or.inl (fun e=>Or.inr (e.resolve_right (fun w=>no ⟨z,w,((mem_neighborFinset _ _ _).mp zm).symm⟩)))))))
    have h := card_le_card ss
    rw [card_neighborFinset_eq_degree] at h
    have i := card_insert_le a (insert b (insert (if G.Adj c x then x else y) (K.erase c)))
    have j := card_insert_le b (insert (if G.Adj c x then x else y) (K.erase c))
    have k := card_insert_le (if G.Adj c x then x else y) (K.erase c)
    have m := card_erase_add_one cm
    have d := high c cm
    have e := k3
    omega
  have nonisolated (c : V) (cm : c∈K) : ∃ z∈K,G.Adj c z := by
    by_contra no
    have ss : G.neighborFinset c⊆insert a (insert b (insert (if G.Adj c x then x else y) W)) := by
      intro z zm
      have n := scope c cm zm
      simp only [mem_insert,mem_union] at n ⊢
      exact n.elim Or.inl (fun e=>Or.inr (e.elim Or.inl (fun e=>Or.inr
        (e.elim Or.inl (fun e=>Or.inr (e.resolve_left (fun w=>no ⟨z,(mem_erase.mp w).2,(mem_neighborFinset _ _ _).mp zm⟩)))))))
    have h := card_le_card ss
    rw [card_neighborFinset_eq_degree] at h
    have i := card_insert_le a (insert b (insert (if G.Adj c x then x else y) W))
    have j := card_insert_le b (insert (if G.Adj c x then x else y) W)
    have k := card_insert_le (if G.Adj c x then x else y) W
    have d := high c cm
    omega
  obtain ⟨c,cm,t,tm,p⟩ := small_common_path nonisolated
  obtain ⟨z,zm,zc⟩ := balance c cm
  exact ⟨c,cm,t,tm,z,zm,p,zc⟩

#print axioms common_exit_balance
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
