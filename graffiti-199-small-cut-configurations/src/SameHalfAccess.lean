import SplitTipsSplice

open private lift_full_cert validFull from SplitTipsLocal

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- With both shared tips on the same side, these are the edges of the
minimal eight-vertex merged region. -/
def sameHalfEdges : List (Fin 8 × Fin 8) :=
  [(0,1),(0,2),(0,3),(1,2),(4,5),(4,1),(4,2),(5,6),(5,7),(6,7)]

private def sameHalfPath (i : Fin 8) : List (Fin 8) :=
  match i with
  | 3 => [6,7,5,4,1,2,0,3]
  | 6 => [3,0,1,2,4,5,7,6]
  | 7 => [3,0,1,2,4,5,6,7]
  | _ => []

private theorem half_cert : ∀ i : Fin 8, i = 3 ∨ i = 6 ∨ i = 7 →
    ∃ a : Fin 8, validFull sameHalfEdges (sameHalfPath i) a i = true := by decide

omit [Fintype V] [DecidableRel G.Adj] in
/-- In the same-half configuration the loose port and the two retained
paired highs are certified endpoints of spanning paths of the merged region. -/
theorem same_half_available_ends (f : Fin 8 ↪ V)
    (edges : ∀ a b, (a,b) ∈ sameHalfEdges → G.Adj (f a) (f b))
    {i : Fin 8} (avail : i = 3 ∨ i = 6 ∨ i = 7) :
    ∃ p : PathOn G (labelRegion f), p.last = f i := by
  obtain ⟨_,cert⟩ := half_cert i avail
  obtain ⟨p,_,last⟩ := lift_full_cert f sameHalfEdges edges cert
  exact ⟨p,last⟩

/-- Four neighbors force the loose port to see outside its singleton
and outside any prescribed set of at most two excluded vertices. -/
theorem PrivateSingleton.loose_has_unblocked_contact (R : PrivateSingleton G)
    {D : Finset V} (small : D.card ≤ 2)
    (looseOff : ¬ G.Adj (R.f 2) (R.f 3)) (degree : 4 ≤ G.degree (R.f 3)) :
    ∃ v ∉ labelRegion R.f, v ∉ D ∧ G.Adj (R.f 3) v := by
  classical
  by_contra no
  have sub : G.neighborFinset (R.f 3) ⊆ insert (R.f 0) D := by
    intro v hv
    have adj := (G.mem_neighborFinset _ _).mp hv
    by_cases inside : v ∈ labelRegion R.f
    · obtain ⟨i,rfl⟩ := inside
      fin_cases i
      · exact Finset.mem_insert_self _ _
      · exact (R.looseNonedge adj.symm).elim
      · exact (looseOff adj.symm).elim
      · exact (G.loopless _ adj).elim
    · have mem : v ∈ D := Classical.byContradiction (fun off => no ⟨v,inside,off,adj⟩)
      exact Finset.mem_insert_of_mem mem
  have h := (Finset.card_le_card sub).trans (Finset.card_insert_le (R.f 0) D)
  rw [G.card_neighborFinset_eq_degree] at h
  omega

/-- After blocking two vertices outside a singleton, deleting its loose port
forces one of its triangle ports to cross to the remaining outside region. -/
theorem PrivateSingleton.triangle_has_unblocked_contact (R : PrivateSingleton G)
    (reach : EdgeReachAfterSmallDeletion G) {D : Finset V}
    (small : D.card ≤ 2) (blockedOutside : ∀ v ∈ D, v ∉ labelRegion R.f)
    {a b : V} (ao : a ∉ labelRegion R.f) (bo : b ∉ labelRegion R.f)
    (aD : a ∉ D) (bD : b ∉ D) (ab : G.Adj a b) :
    ∃ i : Fin 4, (i = 1 ∨ i = 2) ∧ ∃ v ∉ labelRegion R.f, v ∉ D ∧ G.Adj (R.f i) v := by
  classical
  let E := insert (R.f 3) D
  have size : E.card ≤ 3 := by
    have h := Finset.card_insert_le (R.f 3) D
    change (insert (R.f 3) D).card ≤ 3
    omega
  have keep (i : Fin 4) (ne : i ≠ 3) : R.f i ∉ E :=
    fun h => (Finset.mem_insert.mp h).elim (fun e => ne (R.f.injective e))
      (fun d => blockedOutside _ d ⟨i,rfl⟩)
  have outKeep (v : V) (vo : v ∉ labelRegion R.f) (vd : v ∉ D) : v ∉ E :=
    fun h => (Finset.mem_insert.mp h).elim (fun e => vo ⟨3,e.symm⟩) vd
  obtain ⟨u,⟨i,rfl⟩,v,vo,ui,vi,uv⟩ := crossingAfterSmallDeletion reach size
    (U := labelRegion R.f) (a := R.f 0) (b := R.f 1) ⟨0,rfl⟩ ao
    (keep 0 (by decide)) (keep 1 (by decide)) (outKeep a ao aD) (outKeep b bo bD)
    (R.edges 0 1 (by decide)) ab
  have ih := R.outgoing_high vo uv
  have it : i = 1 ∨ i = 2 := by
    fin_cases i
    · cases ih
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (ui (Finset.mem_insert_self _ _)).elim
  exact ⟨i,it,v,vo,fun vd => vi (Finset.mem_insert_of_mem vd),uv⟩

#print axioms same_half_available_ends
#print axioms PrivateSingleton.loose_has_unblocked_contact
#print axioms PrivateSingleton.triangle_has_unblocked_contact

end Graffiti199Depleted
