import ThetaSevenFaithfulCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulBoundary
open SquareCap (boundary)
open PentagonProfile (Port)
open ThetaSevenFaithfulCap (glue link? relation)
noncomputable section

variable {V T : Type*} [Fintype V] [Fintype T]

private theorem in_boundary {G : SimpleGraph V} {c : V → Bool} {e : V × V} :
    e ∈ boundary G c ↔ c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2 := by
  classical
  simp [boundary]

omit [Fintype V] [Fintype T] in
private def sideEdge (p : Port ↪ V) (c : V → Bool)
    (a : Port × T) : (V ⊕ T) × (V ⊕ T) :=
  if c (p a.1) then (Sum.inl (p a.1),Sum.inr (a.2)) else (Sum.inr (a.2),Sum.inl (p a.1))

omit [Fintype V] [Fintype T] in
private theorem inj_sideEdge (p : Port ↪ V) (c : V → Bool) :
    Function.Injective (sideEdge (T:=T) p c) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  unfold sideEdge at h
  split at h <;> split at h <;> simp_all [p.injective.eq_iff]

/-- Exact boundary count: outside, interior gadget, and port wires have
disjoint edge supports; each mismatched wire contributes one edge. -/
theorem glue_boundary (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (wire : Port → T → Bool) (c : V → Bool) (s : T → Bool) :
    (boundary (glue G P p wire) (Sum.elim c s)).card =
      (boundary G c).card + (boundary P s).card + ((univ : Finset (Port × T)).filter (fun a => wire a.1 a.2 = true ∧ c (p a.1) ≠ s a.2)).card := by
  classical
  let i : V ↪ V ⊕ T := ⟨Sum.inl,Sum.inl_injective⟩
  let j : T ↪ V ⊕ T := ⟨Sum.inr,Sum.inr_injective⟩
  let A := (boundary G c).map (i.prodMap i)
  let B := (boundary P s).map (j.prodMap j)
  let X := (univ.filter (fun a : Port × T => wire a.1 a.2 = true ∧ c (p a.1) ≠ s a.2)).image (sideEdge p c)
  have XA (u v : V) : (Sum.inl u,Sum.inl v) ∉ X := by
    intro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    unfold sideEdge at eq
    split at eq <;> simp at eq
  have XB (u v : T) : (Sum.inr u,Sum.inr v) ∉ X := by
    intro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    unfold sideEdge at eq
    split at eq <;> simp at eq
  have split :
      boundary (glue G P p wire) (Sum.elim c s) = (A ∪ B) ∪ X := by
    ext ⟨u,v⟩
    rw [in_boundary,mem_union,mem_union]
    cases u with
    | inl u => cases v with
      | inl v =>
        simp [A,B, i,j, mem_map, Function.Embedding.prodMap, XA,in_boundary,glue,relation,link?]
      | inr v =>
        have left : (c u = true ∧ s v = false ∧ ∃ i, p i = u ∧ wire i v=true) ↔
            (Sum.inl u,Sum.inr v) ∈ X := by
          constructor
          · rintro ⟨ht,hf,a,rfl,ok⟩
            exact mem_image.mpr ⟨(a,v),mem_filter.mpr ⟨mem_univ _,by simp [ht,hf,ok]⟩,by simp [sideEdge,ht]⟩
          · intro h
            obtain ⟨⟨a,k⟩,hi,eq⟩ := mem_image.mp h
            obtain ⟨ok,ne⟩ := (mem_filter.mp hi).2
            unfold sideEdge at eq
            split at eq
            · rename_i ht
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa using eq)
              exact ⟨ht,by cases hs : s k <;> simp_all, a,rfl,ok⟩
            · simp at eq
        simpa [A,B, i,j, mem_map, Function.Embedding.prodMap,glue,relation,link?] using left
    | inr u => cases v with
      | inl v =>
        have left : (s u = true ∧ c v = false ∧ ∃ i, p i = v ∧ wire i u=true) ↔
            (Sum.inr u,Sum.inl v) ∈ X := by
          constructor
          · rintro ⟨ht,hf,a,rfl,ok⟩
            exact mem_image.mpr ⟨(a,u),mem_filter.mpr ⟨mem_univ _,by simp [ht,hf,ok]⟩,by simp [sideEdge,hf]⟩
          · intro h
            obtain ⟨⟨a,k⟩,hi,eq⟩ := mem_image.mp h
            obtain ⟨ok,ne⟩ := (mem_filter.mp hi).2
            unfold sideEdge at eq
            split at eq
            · simp at eq
            · rename_i ht
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa using eq)
              exact ⟨by cases hs : s k <;> simp_all, by simpa using ht,a,rfl,ok⟩
        simpa [A,B, i,j, mem_map, Function.Embedding.prodMap,glue,relation,link?] using left
      | inr v =>
        simp [A,B, i,j, mem_map, Function.Embedding.prodMap, XB, in_boundary,glue,relation,link?]
  have disj1 : Disjoint A B := by
    rw [disjoint_left]
    intro e ha hb
    obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp ha
    simp [B, i,j, mem_map, Function.Embedding.prodMap] at hb
  have disj2 : Disjoint (A ∪ B) X := by
    rw [disjoint_left]
    intro e h hx
    rcases mem_union.mp h with a|b
    · obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp a
      exact XA _ _ hx
    · obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp b
      exact XB _ _ hx
  rw [split, card_union_of_disjoint disj2, card_union_of_disjoint disj1]
  simp [A,B,X,card_image_of_injective _ (inj_sideEdge (T:=T) p c)]

#print axioms glue_boundary
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulBoundary
