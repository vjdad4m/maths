import Tile
import TraceClosure208
import Kelmans

open Finset
namespace Kelmans

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)

omit [DecidableEq V] in
private theorem firstEdges {a b c : V} {tail : List V}
    (h : (a :: b :: c :: tail).Chain' G.Adj) :
    G.Adj a b ∧ G.Adj b c ∧ tail.Chain' G.Adj :=
  ⟨h.rel_head, h.tail.rel_head, h.tail.tail.tail⟩

/-- Same path representation used in the Graffiti #208 closure proof. -/
theorem tiles_of_chain (k : ℕ) (l : List V) (hn : l.Nodup)
    (hc : l.Chain' G.Adj) (hl : l.length = 3*k) :
    Tiles G k l.toFinset := by
  induction k generalizing l with
  | zero =>
    have he : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst l
    simpa using (Tiles.empty : Tiles G 0 ∅)
  | succ k ih =>
    match l with
    | [] => simp at hl
    | [_] | [_,_] => (simp at hl; omega)
    | a :: b :: c :: tail =>
      obtain ⟨hab, hbc, htail⟩ := firstEdges G hc
      let T : Finset V := {a,b,c}
      have hnd : ([a,b,c] : List V).Nodup := by
        apply List.Nodup.sublist _ hn
        exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.nil_sublist _)))
      have hT : T.card = 3 := by
        simpa [T] using List.toFinset_card_of_nodup hnd
      have hCenter : HasCenter G T := by
        refine ⟨b,by simp [T],?_⟩
        intro x hx hxne
        simp only [T,mem_insert,mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hab.symm
        · exact (hxne rfl).elim
        · exact hbc
      have hsub : T ⊆ (a :: b :: c :: tail).toFinset := by
        intro x hx
        simpa [T,or_assoc] using (show x = a ∨ x = b ∨ x = c ∨ x ∈ tail from by
          simp only [T,mem_insert,mem_singleton] at hx
          tauto)
      have hdis : ∀ x ∈ tail, x ∉ T := by
        intro x hx ht
        simp only [T,mem_insert,mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact (List.nodup_cons.mp hn).1 (by simp [hx])
        · exact (List.nodup_cons.mp hn.tail).1 (by simp [hx])
        · exact (List.nodup_cons.mp hn.tail.tail).1 hx
      have hdiff : (a :: b :: c :: tail).toFinset \ T = tail.toFinset := by
        ext x
        simp only [mem_sdiff,List.mem_toFinset,List.mem_cons]
        constructor
        · rintro ⟨h,ht⟩
          rcases h with rfl | rfl | rfl | hm
          · exact (ht (by simp [T])).elim
          · exact (ht (by simp [T])).elim
          · exact (ht (by simp [T])).elim
          · exact hm
        · intro h
          exact ⟨by tauto,hdis x h⟩
      have hlt : tail.length = 3*k := by simp at hl; omega
      exact Tiles.add hsub hT hCenter (hdiff.symm ▸ ih tail hn.tail.tail.tail htail hlt)

theorem tiles_of_traceable [Fintype V] {k : ℕ} (horder : Fintype.card V = 3*k)
    (h : TraceClosure.Traceable G) : Tiles G k univ := by
  obtain ⟨l,hn,hl,hc⟩ := h
  have hfull : l.toFinset = univ := (Finset.card_eq_iff_eq_univ l.toFinset).mp
    (by rw [List.toFinset_card_of_nodup hn,hl])
  rw [← hfull]
  exact tiles_of_chain G k l hn hc (hl.trans horder)

/-- Transfer the earlier #208 edge closure directly to P₃ tilings. -/
theorem tiles_of_traceable_sup_edge [Fintype V] [DecidableRel G.Adj]
    {k : ℕ} (horder : Fintype.card V = 3*k) (x y : V)
    (hd : Fintype.card V - 1 ≤ G.degree x + G.degree y)
    (h : TraceClosure.Traceable (G ⊔ SimpleGraph.edge x y)) : Tiles G k univ :=
  tiles_of_traceable G horder (TraceClosure.traceable_sup_edge G x y hd h)

/-- Connect the search certificate to the public partition formulation. -/
theorem partition_of_tiles {k : ℕ} {U : Finset V} (h : Tiles G k U) :
    ∃ parts : Finset (Finset V),
      (∀ s ∈ parts, KelmansStarter.IsTile G s) ∧
      (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
      parts.biUnion id = U := by
  induction h with
  | empty => exact ⟨∅,by simp⟩
  | @add k U T hsub hthree hcenter rest ih =>
    obtain ⟨parts, hp, hd, hu⟩ := ih
    have hcross : ∀ s ∈ parts, Disjoint T s := by
      intro s hs
      rw [Finset.disjoint_left]
      intro v hv ht
      have hvt : v ∈ parts.biUnion id := Finset.mem_biUnion.mpr ⟨s,hs,ht⟩
      rw [hu] at hvt
      exact (Finset.mem_sdiff.mp hvt).2 hv
    refine ⟨insert T parts, ?_, ?_, ?_⟩
    · intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · exact ⟨hthree,hcenter⟩
      · exact hp s hs
    · intro s hs t ht hne
      rcases mem_insert.mp hs with hst | hs <;> rcases mem_insert.mp ht with htt | ht
      · exact (hne (hst.trans htt.symm)).elim
      · subst s
        exact hcross t ht
      · subst t
        exact (hcross s hs).symm
      · exact hd s hs t ht hne
    · rw [Finset.biUnion_insert,hu]
      ext v
      simp only [id_eq,Finset.mem_union,Finset.mem_sdiff]
      constructor
      · rintro (ht | ⟨hu,_⟩)
        · exact hsub ht
        · exact hu
      · intro hv
        by_cases ht : v ∈ T
        · exact Or.inl ht
        · exact Or.inr ⟨hv,ht⟩

/-- Independent factors on disjoint blocks glue without any cross edges. -/
theorem tiles_union {i j : ℕ} {A B : Finset V} (ha : Tiles G i A)
    (hb : Tiles G j B) (hd : Disjoint A B) : Tiles G (i+j) (A ∪ B) := by
  induction ha with
  | empty => simpa using hb
  | @add k S T hsub hthree hcenter hrest ih =>
    have hD : Disjoint (S \ T) B :=
      hd.mono_left (Finset.sdiff_subset)
    have hTB : Disjoint T B := hd.mono_left hsub
    have he : (S ∪ B) \ T = (S \ T) ∪ B := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hs | hb', ht⟩
        · exact Or.inl ⟨hs,ht⟩
        · exact Or.inr hb'
      · rintro (⟨hs,ht⟩ | hb')
        · exact ⟨Or.inl hs,ht⟩
        · exact ⟨Or.inr hb',fun ht => (Finset.disjoint_left.mp hTB) ht hb'⟩
    rw [show k + 1 + j = (k+j)+1 by omega]
    apply Tiles.add (hsub.trans Finset.subset_union_left) hthree hcenter
    rw [he]
    exact ih hD

/-- One bridge joins a length-1 residue block to a length-2 residue block,
provided the block paths can begin at the bridge endpoints. -/
theorem tiles_of_paired_chains {i j : ℕ} {u v w : V} {A B : List V}
    (ha : (u::A).Nodup) (hb : (v::w::B).Nodup)
    (hd : Disjoint (u::A).toFinset (v::w::B).toFinset)
    (hA : A.Chain' G.Adj) (hB : (v::w::B).Chain' G.Adj)
    (hAB : G.Adj u v) (hAl : A.length = 3*i) (hBl : B.length = 3*j) :
    Tiles G (i+j+1) ((u::A).toFinset ∪ (v::w::B).toFinset) := by
  have huv : u ≠ v := fun h => (Finset.disjoint_left.mp hd) (by simp : u ∈ (u::A).toFinset)
    (by simp [h])
  have huw : u ≠ w := fun h => (Finset.disjoint_left.mp hd) (by simp : u ∈ (u::A).toFinset)
    (by simp [h])
  have hvw : v ≠ w := hB.rel_head.ne
  let T : Finset V := {u,v,w}
  have ht : T.card = 3 := by simp [T,huv,huw,hvw]
  have hcenter : HasCenter G T := (tile_iff_path G T ht).mpr
    ⟨u,v,w,huv,huw,hvw,hAB,hB.rel_head,rfl⟩
  have hsub : T ⊆ (u::A).toFinset ∪ (v::w::B).toFinset := by
    intro x hx
    simp only [T,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  have hrestDisj : Disjoint A.toFinset B.toFinset :=
    hd.mono (by intro x hx; simpa only [List.mem_toFinset,List.mem_cons] using Or.inr (List.mem_toFinset.mp hx))
      (by intro x hx; simp only [List.mem_toFinset,List.mem_cons]; exact Or.inr (Or.inr (List.mem_toFinset.mp hx)))
  refine Tiles.add hsub ht hcenter ?_
  convert tiles_union G (tiles_of_chain G i A ha.tail hA hAl)
    (tiles_of_chain G j B hb.tail.tail hB.tail.tail hBl) hrestDisj using 1
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, List.mem_cons, T,
    mem_insert,mem_singleton,not_or]
  have hAu : u ∉ A := (List.nodup_cons.mp ha).1
  have hBv : v ∉ B := fun h => (List.nodup_cons.mp hb).1 (by simp [h])
  have hBw : w ∉ B := (List.nodup_cons.mp hb.tail).1
  have hAv : v ∉ A := fun h => (Finset.disjoint_left.mp hd) (by simp [h] : v ∈ (u::A).toFinset) (by simp)
  have hAw : w ∉ A := fun h => (Finset.disjoint_left.mp hd) (by simp [h] : w ∈ (u::A).toFinset) (by simp)
  have hBu : u ∉ B := fun h => (Finset.disjoint_left.mp hd) (by simp : u ∈ (u::A).toFinset) (by simp [h])
  by_cases hu : x = u
  · subst x; simp [hAu,hBu]
  by_cases hv : x = v
  · subst x; simp [hAv,hBv]
  by_cases hw : x = w
  · subst x; simp [hAw,hBw]
  simp [hu,hv,hw]

#print axioms tiles_of_paired_chains

theorem kelmans_of_traceable [Fintype V] (hdiv : 6 ∣ Fintype.card V)
    (h : TraceClosure.Traceable G) : KelmansStarter.HasP3Factor G := by
  obtain ⟨m,hm⟩ := hdiv
  have hk : Fintype.card V = 3*(2*m) := by omega
  exact partition_of_tiles G (tiles_of_traceable G hk h)

#print axioms kelmans_of_traceable

#print axioms tiles_of_traceable
#print axioms tiles_of_traceable_sup_edge
end Kelmans
