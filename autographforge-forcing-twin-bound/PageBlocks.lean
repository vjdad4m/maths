import TwinForcing

namespace TwinForcing
open SimpleGraph Finset

abbrev PageVertex (n m : ℕ) := (Fin n × Bool) ⊕ (Fin n × Fin m)

/-- Each pair of hubs is attached to its own m-page block; edges between hubs
may be chosen arbitrarily. This includes both the fan chains and book chains. -/
def pageAdj {n m : ℕ} (H : SimpleGraph (Fin n × Bool)) : PageVertex n m → PageVertex n m → Prop
  | .inl a, .inl b => H.Adj a b
  | .inl a, .inr b => a.1 = b.1
  | .inr a, .inl b => b.1 = a.1
  | .inr _, .inr _ => False

instance {n m : ℕ} (H : SimpleGraph (Fin n × Bool)) [DecidableRel H.Adj] :
    DecidableRel (@pageAdj n m H) := by
  intro x y
  cases x <;> cases y <;> dsimp [pageAdj] <;> infer_instance

def pageGraph {n m : ℕ} (H : SimpleGraph (Fin n × Bool)) : SimpleGraph (PageVertex n m) where
  Adj := pageAdj H
  symm := by
    intro x y e
    cases x <;> cases y
    · exact H.symm e
    · exact e
    · exact e
    · exact e
  loopless := by
    intro x e
    cases x with
    | inl x => exact H.loopless x e
    | inr x => exact e

instance {n m : ℕ} (H : SimpleGraph (Fin n × Bool)) [DecidableRel H.Adj] :
    DecidableRel (@pageGraph n m H).Adj := inferInstanceAs (DecidableRel (@pageAdj n m H))

def pages {n : ℕ} (m : ℕ) (i : Fin n) : Finset (PageVertex n m) :=
  univ.image (fun j : Fin m => Sum.inr (i,j))

theorem pages_card {n m : ℕ} (i : Fin n) : (pages m i).card = m := by
  unfold pages
  rw [card_image_of_injective _ (by
    intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)),card_univ,Fintype.card_fin]

/-- The lower bound for either family, before any planarity, connectivity or
degree-sequence reasoning. The number of hubs joined to other hubs is irrelevant. -/
theorem page_forcing_lower {n m k : ℕ} (H : SimpleGraph (Fin n × Bool)) [DecidableRel H.Adj] :
    n * (m-k) ≤ StarCone.forcing (@pageGraph n m H) k := by
  apply uniform_twin_quota (@pageGraph n m H) (k := k) (B := pages m)
  · intro i w u z hw hu e
    obtain ⟨p,_,rfl⟩ := mem_image.mp hw
    obtain ⟨q,_,rfl⟩ := mem_image.mp hu
    cases z <;> exact e
  · exact pages_card
  · intro i j ne
    rw [Finset.disjoint_left]
    intro x hi hj
    obtain ⟨p,_,rfl⟩ := mem_image.mp hi
    obtain ⟨q,_,same⟩ := mem_image.mp hj
    exact ne (congrArg Prod.fst (Sum.inr.inj same).symm)


/-- With at least three pages per block, the two-forcing lower bound is
attained, irrespective of the graph chosen on the hubs. -/
theorem page_two_forcing_exact {n m : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Fin n × Bool)) [DecidableRel H.Adj] :
    StarCone.forcing (@pageGraph n m H) 2 = n * (m-2) := by
  by_cases hn : n = 0
  · subst n
    have emp : (univ : Finset (PageVertex 0 m)) = ∅ := by
      ext x
      exact Fin.elim0 (Sum.elim Prod.fst Prod.fst x)
    exact le_antisymm (Nat.sInf_le ⟨∅,by simp,by simp [StarCone.full,emp],trivial⟩)
      (by simp)
  let G := @pageGraph n m H
  let zero : Fin m := ⟨0,by omega⟩
  let one : Fin m := ⟨1,by omega⟩
  let two : Fin m := ⟨2,by omega⟩
  have ne10 : one ≠ zero := by intro e; have := congrArg Fin.val e; contradiction
  have ne20 : two ≠ zero := by intro e; have := congrArg Fin.val e; contradiction
  have ne21 : two ≠ one := by intro e; have q := congrArg Fin.val e; change 2 = 1 at q; omega
  let S : Finset (PageVertex n m) :=
    (univ.product ((univ.erase zero).erase one)).image Sum.inr
  have sc : S.card = n*(m-2) := by
    dsimp [S]
    rw [card_image_of_injective _ Sum.inr_injective,card_product,card_univ,Fintype.card_fin,
      card_erase_of_mem (mem_erase.mpr ⟨ne10,mem_univ _⟩),
      card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
    rw [Nat.sub_sub]
  have seed (i : Fin n) (j : Fin m) (h0 : j ≠ zero) (h1 : j ≠ one) :
      (Sum.inr (i,j) : PageVertex n m) ∈ S :=
    mem_image.mpr ⟨(i,j),mem_product.mpr ⟨mem_univ _,mem_erase.mpr
      ⟨h1,mem_erase.mpr ⟨h0,mem_univ _⟩⟩⟩,rfl⟩
  have stays (T : Finset (PageVertex n m)) : T ⊆ StarCone.step G 2 T := by
    intro x hx
    exact mem_union.mpr (Or.inl hx)
  have enters (T : Finset (PageVertex n m)) {x y : PageVertex n m} (hx : x ∈ T)
      (adj : G.Adj x y) (bound : (G.neighborFinset x \ T).card ≤ 2) :
      y ∈ StarCone.step G 2 T := by
    by_cases hy : y ∈ T
    · exact stays T hy
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,hy,x,hx,adj,bound⟩))
  let T := StarCone.step G 2 S
  have allHubs (i : Fin n) (b : Bool) : Sum.inl (i,b) ∈ T := by
    apply enters S (seed i two ne20 ne21)
    · rfl
    have sub : G.neighborFinset (Sum.inr (i,two)) \ S ⊆ {Sum.inl (i,false),Sum.inl (i,true)} := by
      intro x hx
      have e := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1
      rcases x with ⟨j,b'⟩|⟨j,p⟩
      · change j = i at e
        subst j
        cases b' <;> simp
      · exact False.elim e
    exact (card_le_card sub).trans Finset.card_le_two
  have complete : StarCone.step G 2 T = univ := by
    apply eq_univ_of_forall
    intro x
    rcases x with ⟨i,b⟩|⟨i,p⟩
    · exact stays T (allHubs i b)
    apply enters T (allHubs i false)
    · rfl
    have sub : G.neighborFinset (Sum.inl (i,false)) \ T ⊆
        {Sum.inr (i,zero),Sum.inr (i,one)} := by
      intro x hx
      have out := (mem_sdiff.mp hx).2
      have e := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1
      rcases x with ⟨j,b⟩|⟨j,q⟩
      · exact False.elim (out (allHubs j b))
      · change i = j at e
        subst j
        by_cases h0 : q = zero
        · simp [h0]
        by_cases h1 : q = one
        · simp [h1]
        exact False.elim (out (stays S (seed i q h0 h1)))
    exact (card_le_card sub).trans Finset.card_le_two
  have rounds : 2 ≤ Fintype.card (PageVertex n m) := by
    have h : 1 ≤ n := by omega
    rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  have hf : StarCone.full G 2 S := by
    unfold StarCone.full
    have rr : Fintype.card (PageVertex n m) = (Fintype.card (PageVertex n m)-2) + 2 := by omega
    rw [rr,Function.iterate_add_apply]
    have h2 : (StarCone.step G 2)^[2] S = univ := complete
    rw [h2]
    have fixed : StarCone.step G 2 univ = univ := by simp [StarCone.step]
    exact Function.iterate_fixed fixed _
  exact le_antisymm (Nat.sInf_le ⟨S,sc,hf,trivial⟩) (page_forcing_lower H)

#print axioms page_forcing_lower
#print axioms page_two_forcing_exact
end TwinForcing
