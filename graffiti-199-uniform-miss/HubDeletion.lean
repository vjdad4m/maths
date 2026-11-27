import CubicPairReduction
open private reach_of_map_or_eq from CutTorso
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {x p r y : V}
abbrev HubKeep (x p : V) := {v : V | v ≠ x ∧ v ≠ p}

theorem hubKeep_card (xp : x ≠ p) : Fintype.card (HubKeep x p) = Fintype.card V - 2 := by
  classical
  have eq : HubKeep x p = ((↑({x,p} : Finset V) : Set V)ᶜ) := by ext; simp [HubKeep]
  calc
    _ = _ := Fintype.card_congr (Equiv.setCongr eq)
    _ = _ := ?_
  change Fintype.card {v : V // v ∉ ({x,p} : Finset V)} = _
  rw [Fintype.card_subtype_compl]
  change Fintype.card V - Fintype.card (↑({x,p} : Finset V)) = _
  rw [Fintype.card_coe,Finset.card_pair xp]

/-- Deleting two vertices preserves three-connectivity when one is the only
cubic neighbor of the other and its surviving neighbors can be joined through
a common neighbor after each further two-vertex deletion. -/
theorem connectivity_after_hub_pair (conn : ConnectivityAtLeast G 3)
    (order : 6 ≤ Fintype.card V) (cross : CrossingBetweenSurvivingEdges G)
    (xp : x ≠ p) (safe : ∀ v, G.Adj x v → G.degree v = 3 → v = p)
    {J : SimpleGraph (HubKeep x p)} (leJ : G.induce (HubKeep x p) ≤ J)
    (bypass : ∀ D : Finset (HubKeep x p), D.card < 3 →
      ∃ h : Survives D, ∀ v : Survives D, G.Adj p v.val.val →
        J.Adj h.val v.val ∨ h = v) :
    ConnectivityAtLeast J 3 := by
  classical
  let S := HubKeep x p
  let H := J
  have sz := hubKeep_card xp
  refine ⟨(by omega),?_⟩
  intro D small
  let emb : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let K := insert x (D.map emb)
  have ksmall : K.card ≤ 3 := by
    have h := Finset.card_insert_le x (D.map emb); rw [Finset.card_map] at h; dsimp [K]; omega
  let back (v : Survives D) : Survives K := ⟨v.val.val,by
    rintro mem
    rcases Finset.mem_insert.mp mem with e|m
    · exact v.val.property.1 e
    · obtain ⟨b,bD,e⟩ := Finset.mem_map.mp m
      exact v.property ((show b = v.val from Subtype.ext e) ▸ bD)⟩
  have incident (v : Survives D) : ∃ w : Survives K, G.Adj (back v).val w.val := by
    by_contra! none
    have sub : G.neighborFinset v.val.val ⊆ K := by
      intro w m
      by_contra off
      exact none ⟨w,off⟩ ((G.mem_neighborFinset _ _).mp m)
    have lo := degree_of_small_deletion_preconnected (G := G) (by omega : 4 ≤ Fintype.card V)
      (fun U hU => (conn.2 U hU).preconnected) v.val.val
    have hi := Finset.card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at hi
    have eq := Finset.eq_of_subset_of_card_le sub (by rw [G.card_neighborFinset_eq_degree]; omega)
    have hx : x ∈ G.neighborFinset v.val.val := eq.symm ▸ Finset.mem_insert_self x _
    exact v.val.property.2 (safe _ ((G.mem_neighborFinset _ _).mp hx).symm (by omega))
  obtain ⟨h,bp⟩ := bypass D small
  let keep (v : Survives K) (vp : v.val ≠ p) : Survives D :=
    ⟨⟨v.val,fun e => v.property (by simp [K,e]),vp⟩,fun m =>
      v.property (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨_,m,rfl⟩))⟩
  let f (v : Survives K) : Survives D := if e : v.val = p then h else keep v e
  have fb (v : Survives D) : f (back v) = v := by simp [f,back,v.val.property.2,keep]
  have map (s t : Survives K) (e : (DeletionGraph G K).Adj s t) :
      (DeletionGraph H D).Adj (f s) (f t) ∨ f s = f t := by
    change G.Adj s.val t.val at e
    by_cases se : s.val = p <;> by_cases te : t.val = p
    · exact (e.ne (se.trans te.symm)).elim
    · simpa only [f,dif_pos se,dif_neg te] using bp (keep t te) (by simpa only [← se] using e)
    · rcases bp (keep s se) (by simpa only [← te] using e.symm) with ed|eq
      · exact Or.inl (by simpa only [f,dif_neg se,dif_pos te] using ed.symm)
      · exact Or.inr (by simpa only [f,dif_neg se,dif_pos te] using eq.symm)
    · exact Or.inl (by simpa only [f,dif_neg se,dif_neg te] using leJ (show (G.induce S).Adj (keep s se).val (keep t te).val from e))
  have pre : (DeletionGraph H D).Preconnected := by
    intro s t
    obtain ⟨u,su⟩ := incident s
    obtain ⟨v,tv⟩ := incident t
    have hst := edgeReach_iff_crossing_between_surviving_edges.mpr cross K ksmall (back s) u (back t) v su tv
    simpa only [fb] using reach_of_map_or_eq f map hst
  have proper : D.card < (Finset.univ : Finset S).card := by rw [Finset.card_univ]; change D.card < Fintype.card (HubKeep x p); omega
  obtain ⟨v,_,vo⟩ := Finset.exists_mem_not_mem_of_card_lt_card proper
  exact @SimpleGraph.Connected.mk _ (DeletionGraph H D) pre ⟨⟨v,vo⟩⟩

#print axioms connectivity_after_hub_pair
end Graffiti199Depleted.Catalogue.Incomplete


