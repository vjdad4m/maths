import OneGate180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem part_eq_of_closed (J : SimpleGraph V) (R H : Finset V) (a : V)
    (ah : a∈H) (hr : H⊆R) (conn : Con J H)
    (closed : ∀ i∈H,∀ j∈R,J.Adj i j → j∈H) : part J R a=H := by
  classical
  ext t
  rw [mem_part]
  constructor
  · rintro ⟨_,⟨p⟩⟩
    have move {s v : V} (q : (within J R).Walk s v) : s∈H → v∈H := by
      induction q with
      | nil => exact id
      | cons e _ ih => exact fun h => ih (closed _ h _ e.2.2 e.1)
    exact move p ah
  · intro th
    obtain ⟨p⟩ := conn (⟨a,ah⟩ : ↥(H : Set V)) ⟨t,th⟩
    have go {s v : ↥(H : Set V)} (q : (J.induce (H:Set V)).Walk s v) :
        (within J R).Reachable s.val v.val := by
      induction q with
      | nil => exact .refl _
      | @cons i j k e _ ih =>
        exact (show (within J R).Adj i.val j.val from ⟨e,hr i.property,hr j.property⟩).reachable.trans ih
    exact ⟨hr th,go p⟩

omit [Fintype V] in
theorem remote_eq_singleton (J : SimpleGraph V) (R D H : Finset V) (y a : V)
    (cover : R=D∪H) (yd : y∈D) (ah : a∈H) (dh : Disjoint D H) (cd : Con J D) (ch : Con J H)
    (apart : ∀ i∈D,∀ j∈H,¬J.Adj i j) : remote J R y={H} := by
  classical
  have dsub : D⊆R := cover ▸ subset_union_left
  have hsub : H⊆R := cover ▸ subset_union_right
  have dpart {i : V} (h : i∈D) : part J R i=D := by
    apply part_eq_of_closed J R D i h dsub cd
    intro t ht j jr e
    rcases mem_union.mp (cover ▸ jr) with fits|other
    · exact fits
    · exact (apart t ht j other e).elim
  have hpart {i : V} (h : i∈H) : part J R i=H := by
    apply part_eq_of_closed J R H i h hsub ch
    intro t ht j jr e
    rcases mem_union.mp (cover ▸ jr) with other|fits
    · exact (apart j other t ht e.symm).elim
    · exact fits
  have ne : H≠D := fun eq => (disjoint_left.mp dh yd) (eq ▸ yd)
  ext T
  simp only [remote,mem_erase,mem_image,mem_singleton]
  constructor
  · rintro ⟨other,i,ir,rfl⟩
    rcases mem_union.mp (cover ▸ ir) with id'|ih
    · exact (other ((dpart id').trans (dpart yd).symm)).elim
    · exact hpart ih
  · rintro rfl
    exact ⟨fun e => ne (e.trans (dpart yd)),a,hsub ah,hpart ah⟩

/-- If precisely one other component survives a pair release and that
component has only one gate into the pair, the graph supplies a returned
old leaf. The winning set replaces exactly two old leaves by the given pair. -/
theorem saturated_pair (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z H : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y) (pair : Z.card=2)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (sat : ∀ b∈C.erase x,J.Adj x b)
    (feed : ∀ z∈Z,Dominates J ((univ\C)\Z) z)
    (one : remote J ((univ\C)\Z) y={H})
    (gate : ∃ z∈Z,∀ i∈H,∀ j∈Z,J.Adj i j → j=z) :
    FirstForm J U x y w ∧ ∃ b∈C.erase x, let L := (C.erase x).erase b ∪ Z
      L⊆U\{x,y} ∧ L.card=C.card ∧ L\C=Z ∧ C\L={x,b} ∧
      Con (J⊔SimpleGraph.edge x y) (univ\L) ∧ ∀ q∈L,Dominates (J⊔SimpleGraph.edge x y) (univ\L) q := by
  classical
  let R := (univ\C)\Z
  have zs' : Z⊆(univ\C).erase y := by
    intro t h
    obtain ⟨ty,tc⟩ := mem_erase.mp (zs h)
    exact mem_erase.mpr ⟨ty,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp tc).2⟩⟩
  have hH : H∈remote J R y := one ▸ mem_singleton_self _
  obtain ⟨b,bc,bd⟩ := contact_of_one_gate J C Z x y tip zs' nc H hH gate
  have yr : y∈R := mem_sdiff.mpr ⟨tip.2.1,fun h => (mem_erase.mp (zs h)).1 rfl⟩
  have hit (i : V) (ir : i∈R) :
      Dominates J (part J R i) b ∨ (J.Adj x b ∧ (within J R).Reachable i y) := by
    by_cases same : part J R i=part J R y
    · have h : y∈part J R i := same ▸ (mem_part ..).mpr ⟨yr,.refl _⟩
      exact Or.inr ⟨sat b bc,((mem_part ..).mp h).2⟩
    · have k : part J R i∈remote J R y := mem_erase.mpr ⟨same,mem_image_of_mem _ ir⟩
      have eq : part J R i=H := mem_singleton.mp (one ▸ k)
      exact Or.inl (eq ▸ bd)
  have served (q : V) (h : q∈demand J R C Z x) : q=b ∨ J.Adj q b := by
    obtain ⟨place,nr,nx⟩ := (mem_demand ..).mp h
    rcases mem_union.mp place with k|k
    · exact (nx (sat q k).symm).elim
    · exact (nr (feed q k)).elim
  have result := pair_exchange_iff J C Z x y b xy tip bc zs'
  dsimp only at result
  obtain ⟨con,dom⟩ := result.mpr ⟨hit,served⟩
  let L := (C.erase x).erase b ∪ Z
  have zc {q:V} (qz:q∈Z) : q∉C := (mem_sdiff.mp (mem_of_mem_erase (zs qz))).2
  have dis : Disjoint ((C.erase x).erase b) Z := disjoint_left.mpr
    (fun _ k z => zc z (mem_of_mem_erase (mem_of_mem_erase k)))
  have nL : L.card=((C.erase x).erase b).card+Z.card := card_union_of_disjoint dis
  have nC := card_erase_add_one tip.1
  have nB := card_erase_add_one bc
  have prevented : y∉C := (mem_sdiff.mp tip.2.1).2
  refine ⟨first_of_pair_exchange J hc hn x y w b xy old xw wy U C Z cu count tip bc zs pair.ge hit served,
    b,bc,?_,by change L.card=C.card; rw [nL]; omega,?_,?_,con,dom⟩
  · intro q h
    rcases mem_union.mp h with k|k
    · obtain ⟨qx,qc⟩ := mem_erase.mp (mem_of_mem_erase k)
      exact mem_sdiff.mpr ⟨cu qc,by simp [qx,show q≠y from fun e => prevented (e ▸ qc)]⟩
    · obtain ⟨qy,qu⟩ := mem_erase.mp (zs k)
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp qu).1,by simp [qy,show q≠x from fun e => zc k (e ▸ tip.1)]⟩
  · ext q
    simp only [L,mem_sdiff,mem_union,mem_erase]
    have := @zc q
    tauto
  · ext q
    constructor
    · intro h
      obtain ⟨qc,out⟩ := mem_sdiff.mp h
      by_cases qx : q=x
      · exact mem_insert.mpr (Or.inl qx)
      by_cases qb : q=b
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr qb))
      exact (out (mem_union_left _ (mem_erase.mpr ⟨qb,mem_erase.mpr ⟨qx,qc⟩⟩))).elim
    · intro h
      have e : q=x ∨ q=b := by simpa only [mem_insert,mem_singleton] using h
      have qc : q∈C := e.elim (fun h => h ▸ tip.1) (fun h => h ▸ mem_of_mem_erase bc)
      refine mem_sdiff.mpr ⟨qc,?_⟩
      intro hl
      rcases mem_union.mp hl with k|k
      · obtain ⟨qb,k⟩ := mem_erase.mp k
        exact e.elim (fun eq => (mem_erase.mp k).1 eq) qb
      · exact zc k qc

#print axioms remote_eq_singleton
#print axioms saturated_pair
end Minimal180.Controlled
