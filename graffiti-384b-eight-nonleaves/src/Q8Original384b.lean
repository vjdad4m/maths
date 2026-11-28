import OddQuota384b

namespace Graffiti384b.Q8Original
open Finset SimpleGraph
open private OddQuota.core_data from OddQuota384b
open private TrianglePrune.induced_cost from TrianglePrune384b

private def links {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (w : W) :=
  ((H.neighborFinset w).powersetCard 2).filter
    (fun p => ∀ x ∈ p, ∀ y ∈ p, x ≠ y → H.Adj x y)

private theorem mem_links {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (w : W) (p : Finset W) :
    p∈links H w ↔ p.card=2 ∧ (∀ x∈p, H.Adj w x) ∧
      (∀ x∈p, ∀ y∈p, x≠y → H.Adj x y) := by
  simp only [links, mem_filter, mem_powersetCard, Finset.subset_iff, mem_neighborFinset]
  tauto

private theorem map_links {W X : Type*} [Fintype W] [Fintype X] [DecidableEq W] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (e : W ≃ X) (w : W) :
    (links (H.comap e) w).image (Finset.map e.toEmbedding) = links H (e w) := by
  ext p; constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨two,nei,adj⟩ := (mem_links _ _ _).mp hq
    apply (mem_links _ _ _).mpr
    refine ⟨by simpa using two,?_,?_⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      exact nei a ha
    · intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      exact adj a ha b hb (fun h => hxy (congrArg e h))
  · intro hp
    obtain ⟨two,nei,adj⟩ := (mem_links _ _ _).mp hp
    have hm : (p.map e.symm.toEmbedding).map e.toEmbedding = p := by simp [Finset.map_map]
    refine mem_image.mpr ⟨p.map e.symm.toEmbedding,?_,hm⟩
    apply (mem_links _ _ _).mpr
    refine ⟨by simpa using two,?_,?_⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      change H.Adj (e w) (e (e.symm a))
      simpa using nei a ha
    · intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      change H.Adj (e (e.symm a)) (e (e.symm b))
      simpa using adj a ha b hb (fun h => hxy (congrArg e.symm h))

private theorem triangle_comap {W X : Type*} [Fintype W] [Fintype X] [DecidableEq W] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (e : W ≃ X) (w : W) :
    trianglesAt (H.comap e) w = trianglesAt H (e w) := by
  change (links (H.comap e) w).card = (links H (e w)).card
  rw [← map_links H e w, card_image_of_injective _ (Finset.map_injective e.toEmbedding)]

private theorem gamma_le_comap {W X : Type*} [Fintype W] [Fintype X] [DecidableEq W] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (e : W ≃ X) :
    gamma H ≤ gamma (H.comap e) := by
  let K := H.comap (e : W→X)
  have av : {k : ℕ | ∃ d, TwoDominates K d ∧ d.card=k}.Nonempty :=
    ⟨_,Finset.univ,by simp [TwoDominates],rfl⟩
  obtain ⟨d,dom,dc⟩ := Nat.sInf_mem av
  change d.card=gamma K at dc
  let D := d.map e.toEmbedding
  have good : TwoDominates H D := by
    intro x hx
    have outside : e.symm x ∉ d := fun m =>
      hx (mem_map.mpr ⟨e.symm x,m,e.apply_symm_apply x⟩)
    have sub : (d.filter (K.Adj (e.symm x))).map e.toEmbedding ⊆ D.filter (H.Adj x) := by
      intro y hy
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
      obtain ⟨mz,adj⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_map.mpr ⟨z,mz,rfl⟩,by
        change H.Adj (e (e.symm x)) (e z) at adj
        simpa using adj⟩
    have h := card_le_card sub
    rw [card_map] at h
    exact (dom (e.symm x) outside).trans h
  change gamma H≤gamma K
  rw [← dc,← Finset.card_map e.toEmbedding]
  exact Nat.sInf_le ⟨D,good,rfl⟩

/-- The Fin 8 quota implies the original-graph inequality for eight
nonleaves and at least nine triangle types, without a connectivity premise. -/
theorem nonleaf_eight_of_fin8_quota
    (quota : ∀ (H : SimpleGraph (Fin 8)) (dh : DecidableRel H.Adj),
      letI := dh
      (∀ v, 0 < trianglesAt H v) → Function.Injective (trianglesAt H) → gamma H ≤ 3)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (eight : (nonleaves G).card=8) (nine : 9≤(types G).card) : gamma G ≤ bound G := by
  let P := nonleaves G
  let H := G.induce (P : Set V)
  obtain ⟨eq,pos,inj⟩ := OddQuota.core_data G (by omega : (nonleaves G).card<(types G).card)
  change (types G).card=P.card+1 at eq
  change (∀ v,0<trianglesAt H v) at pos
  change Function.Injective (trianglesAt H) at inj
  let e : Fin 8 ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P |>.trans eight)).symm
  let K := H.comap (e : Fin 8→P)
  let dk : DecidableRel K.Adj := inferInstanceAs (DecidableRel (H.comap (e : Fin 8→P)).Adj)
  have hp (v : Fin 8) : 0<trianglesAt K v := by
    change 0<trianglesAt (H.comap e) v
    rw [triangle_comap]
    exact pos (e v)
  have hi : Function.Injective (trianglesAt K) := by
    intro v w h
    change trianglesAt (H.comap e) v = trianglesAt (H.comap e) w at h
    rw [triangle_comap,triangle_comap] at h
    exact e.injective (inj h)
  have core : gamma H≤3 := (gamma_le_comap H e).trans (quota K dk hp hi)
  have cost := TrianglePrune.induced_cost G P
  change P.card≤gamma H+Capacity.value G P ∅ at cost
  have more := Capacity.mono_kept G (r:=P) (empty_subset Pᶜ)
  have rooted := OddQuota.rooted_value G
  change gamma G+Capacity.value G P Pᶜ=Fintype.card V at rooted
  change P.card=8 at eight
  unfold bound
  omega

end Graffiti384b.Q8Original

#print axioms Graffiti384b.Q8Original.nonleaf_eight_of_fin8_quota
