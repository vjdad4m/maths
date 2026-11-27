import SpareChord

open Finset
namespace KelmansCactus.Assemble
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure LocalPart (P : Finset (Finset V)) (S : Finset V) : Prop where
  tile : ∀ t ∈ P, KelmansStarter.IsTile G t
  disj : ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t
  cover : P.biUnion id = S

omit [Fintype V] in
theorem tile_sub_union {t : Finset V} {P : Finset (Finset V)} (ht : t ∈ P) :
    t ⊆ P.biUnion id :=
  fun _ h => mem_biUnion.mpr ⟨t,ht,h⟩

omit [Fintype V] in
theorem LocalPart.tile_sub {S : Finset V} {t : Finset V} {P : Finset (Finset V)}
    (h : LocalPart G P S) (ht : t ∈ P) : t ⊆ S :=
  h.cover ▸ tile_sub_union ht

/-- Exact decomposition principle for any number of cycles or residual
regions. Choose the boundary tiles E first; the remaining path-factor
problems on disjoint cells can then be solved independently. Any cell
may have an arbitrary internal shape; all its edges to other cells
are forbidden (all exits land in W). This is an equivalence, not
merely a necessary residue condition. -/
theorem factor_iff_boundary {I : Type*} {J : Finset I} {D : I → Finset V} {W : Finset V}
    (cells : (J : Set I).PairwiseDisjoint D)
    (cover : ∀ v ∉ W, ∃ i ∈ J, v ∈ D i)
    (ex : ∀ i ∈ J, ∀ u ∈ D i, ∀ v ∉ D i, G.Adj u v → v ∈ W) :
    KelmansStarter.HasP3Factor G ↔
      ∃ E : Finset (Finset V), LocalPart G E (E.biUnion id) ∧
        W ⊆ E.biUnion id ∧ ∀ i ∈ J, ∃ P, LocalPart G P (D i \ E.biUnion id) := by
  classical
  constructor
  · rintro ⟨P,ht,hd,hu⟩
    let E := P.filter fun t => ¬ Disjoint t W
    have hE : E ⊆ P := filter_subset _ _
    refine ⟨E,⟨fun t he => ht t (hE he),fun s hs t ht' ne => hd s (hE hs) t (hE ht') ne,rfl⟩,?_,?_⟩
    · intro v hv
      have hPu : v ∈ P.biUnion id := hu.symm ▸ mem_univ _
      obtain ⟨t,ht',vt⟩ := mem_biUnion.mp hPu
      have he : t ∈ E :=
        mem_filter.mpr ⟨ht',fun h => disjoint_left.mp h vt hv⟩
      exact mem_biUnion.mpr ⟨t,he,vt⟩
    · intro i hi
      let Q := P.filter fun t => t ⊆ D i ∧ t ∉ E
      have hQ : Q ⊆ P := filter_subset _ _
      refine ⟨Q,⟨fun t hq => ht t (hQ hq),fun s hs t ht' ne => hd s (hQ hs) t (hQ ht') ne,?_⟩⟩
      ext v
      constructor
      · intro hv
        obtain ⟨t,hqt,hvt⟩ := mem_biUnion.mp hv
        obtain ⟨hpt,sub,tne⟩ := mem_filter.mp hqt
        refine mem_sdiff.mpr ⟨sub hvt,?_⟩
        intro hve
        obtain ⟨s,hse,hvs⟩ := mem_biUnion.mp hve
        have eq : t = s := by
          by_contra ne
          exact disjoint_left.mp (hd t hpt s (hE hse) ne) hvt hvs
        exact tne (eq.symm ▸ hse)
      · intro hv
        obtain ⟨vD,vE⟩ := mem_sdiff.mp hv
        have hPu : v ∈ P.biUnion id := hu.symm ▸ mem_univ _
        obtain ⟨t,hpt,hvt⟩ := mem_biUnion.mp hPu
        have tE : t ∉ E := fun he => vE (mem_biUnion.mpr ⟨t,he,hvt⟩)
        have hsub : t ⊆ D i := by
          intro w wt
          by_contra wn
          obtain ⟨p,pt,pW⟩ := SpareChord.mixed_has_port G (ex i hi) (ht t hpt)
            ⟨⟨v,hvt,vD⟩,⟨w,wt,wn⟩⟩
          exact tE (mem_filter.mpr ⟨hpt,fun dj => disjoint_left.mp dj pt pW⟩)
        exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨hpt,hsub,tE⟩,hvt⟩
  · rintro ⟨E,he,hW,hD⟩
    have hD' (i : {x // x ∈ J}) : ∃ P, LocalPart G P (D i.val \ E.biUnion id) :=
      hD i.val i.property
    choose P hP using hD'
    let Q := J.attach.biUnion P
    have Qmem {t : Finset V} (ht : t ∈ Q) : ∃ i, t ∈ P i := by
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp ht
      exact ⟨i,hi⟩
    have EvsQ {s t : Finset V} (hs : s ∈ E) (ht : t ∈ Q) : Disjoint s t := by
      obtain ⟨i,hi⟩ := Qmem ht
      exact disjoint_left.mpr fun v vs vt =>
        (mem_sdiff.mp ((hP i).tile_sub G hi vt)).2 (tile_sub_union hs vs)
    refine ⟨E ∪ Q, ?_, ?_, ?_⟩
    · intro t ht
      rcases mem_union.mp ht with ht | ht
      · exact he.tile t ht
      · obtain ⟨i,hi⟩ := Qmem ht
        exact (hP i).tile t hi
    · intro s hs t ht ne
      rcases mem_union.mp hs with hs | hs <;> rcases mem_union.mp ht with ht | ht
      · exact he.disj s hs t ht ne
      · exact EvsQ hs ht
      · exact (EvsQ ht hs).symm
      · obtain ⟨i,hi⟩ := Qmem hs
        obtain ⟨j,hj⟩ := Qmem ht
        by_cases eq : i = j
        · subst j
          exact (hP i).disj s hi t hj ne
        · have nv : i.val ≠ j.val := fun h => eq (Subtype.ext h)
          exact (cells i.property j.property nv).mono
            (((hP i).tile_sub G hi).trans sdiff_subset)
            (((hP j).tile_sub G hj).trans sdiff_subset)
    · apply eq_univ_of_forall
      intro v
      by_cases inE : v ∈ E.biUnion id
      · obtain ⟨t,ht,vt⟩ := mem_biUnion.mp inE
        exact mem_biUnion.mpr ⟨t,mem_union_left _ ht,vt⟩
      · obtain ⟨i,hi,vi⟩ := cover v (fun vw => inE (hW vw))
        let i' : {x // x ∈ J} := ⟨i,hi⟩
        have vlocal : v ∈ (P i').biUnion id :=
          (hP i').cover.symm ▸ mem_sdiff.mpr ⟨vi,inE⟩
        obtain ⟨t,tp,vt⟩ := mem_biUnion.mp vlocal
        exact mem_biUnion.mpr ⟨t,mem_union_right _ (mem_biUnion.mpr ⟨i',mem_attach _ _,tp⟩),vt⟩

#print axioms factor_iff_boundary
end KelmansCactus.Assemble
