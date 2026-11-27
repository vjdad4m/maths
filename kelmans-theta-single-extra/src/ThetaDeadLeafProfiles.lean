import ThetaAdjacentEarLeafModes

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaDeadLeafProfiles
open SquareCap (IsTile)
open ThetaFiveModes (mid leaf Lane)
open ThetaAdjacentEarLeafModes (WeakLayout)
noncomputable section

variable {V : Type*} [DecidableEq V]

private theorem three_card {T : Type*} [DecidableEq T] {a b c : T}
    (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ({a,b,c}:Finset T).card=3 := by
  simp [card_insert_of_not_mem,ab,ac,bc]

private theorem third {T : Type*} [DecidableEq T] {S : Finset T} {a b : T}
    (sz : S.card=3) (aS : a∈S) (bS : b∈S) (ab : a≠b) :
    ∃ w,w∈S ∧ w≠a ∧ w≠b ∧ S={a,b,w} := by
  have p : ({a,b}:Finset T).card=2 := by simp [card_insert_of_not_mem,ab]
  obtain ⟨w,hw,hide⟩ := exists_mem_not_mem_of_card_lt_card (by omega :
    ({a,b}:Finset T).card<S.card)
  have wa : w≠a := fun h=>hide (by simp [h])
  have wb : w≠b := fun h=>hide (by simp [h])
  refine ⟨w,hw,wa,wb,?_⟩
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  · rw [sz,three_card ab wa.symm wb.symm]


omit [DecidableEq V] in
private theorem tags (k : Fin 3) :
    (Sum.inr k : V⊕Fin 3)=mid ∨ Sum.inr k=leaf (V:=V) false ∨
      Sum.inr k=leaf (V:=V) true := by
  have dec : ∀ k : Fin 3,k=0∨k=1∨k=2 := by decide
  rcases dec k with rfl|rfl|rfl <;> simp [mid,leaf]

def MidLayout (C : SimpleGraph (V⊕Fin 3)) (m : V) : Prop :=
  ∀ x,C.Adj mid x → x=leaf false ∨ x=leaf true ∨ x=.inl m

/-- A tile using both live virtual vertices must use one of
the three possible live wires. The two virtual vertices
cannot have the exterior vertex as their common center. -/
theorem shared_profile {C : SimpleGraph (V⊕Fin 3)} {m : V} {p : Lane↪V}
    (L : WeakLayout C p) (M : MidLayout C m)
    (distinct : ∀ i : Bool,m≠p (false,i))
    {S : Finset (V⊕Fin 3)} (tile : IsTile C S) (md : mid∈S) (lf : leaf false∈S)
    (dead : leaf true∉S) :
    ∃ v : V,S={mid,leaf false,.inl v} ∧
    ((v=m ∧ C.Adj mid (.inl v)) ∨
      ∃ i : Bool,v=p (false,i) ∧ C.Adj (leaf false) (.inl v)) := by
  obtain ⟨sz,c,hc,star⟩ := tile
  obtain ⟨z,zs,zm,zf,shape⟩ := third sz md lf (by simp [leaf,mid])
  cases z with
  | inr k =>
    rcases tags (V:=V) k with e|e|e
    · exact (zm e).elim
    · exact (zf e).elim
    · exact (dead (e ▸ zs)).elim
  | inl v =>
    refine ⟨v,shape,?_⟩
    have hC : c=mid ∨ c=leaf false ∨ c=Sum.inl v := by simpa [shape] using hc
    rcases hC with rfl|rfl|rfl
    · have E := star (.inl v) zs zm
      rcases M _ E with e|e|e
      · simp [leaf] at e
      · simp [leaf] at e
      · exact Or.inl ⟨Sum.inl_injective e,E⟩
    · have E := star (.inl v) zs zf
      rcases L.leafAdj false _ E with e|e|e
      · exact False.elim (zm e)
      · exact Or.inr ⟨false,Sum.inl_injective e,E⟩
      · exact Or.inr ⟨true,Sum.inl_injective e,E⟩
    · have a := M _ (star mid md (fun e=>zm e.symm)).symm
      have b := L.leafAdj false _ (star (leaf false) lf (fun e=>zf e.symm)).symm
      have vm : v=m := by
        rcases a with e|e|e
        · simp [leaf] at e
        · simp [leaf] at e
        · exact Sum.inl_injective e
      rcases b with e|e|e
      · exact (zm e).elim
      · exact (distinct false (vm.symm.trans (Sum.inl_injective e))).elim
      · exact (distinct true (vm.symm.trans (Sum.inl_injective e))).elim

/-- Once the retained leaf is in another tile, the midpoint has
only one possible wire and must be an endpoint on its tile. -/
theorem split_mid_profile {C : SimpleGraph (V⊕Fin 3)} {m : V}
    (M : MidLayout C m) {S : Finset (V⊕Fin 3)} (tile : IsTile C S)
    (md : mid∈S) (lf : leaf false∉S) (dead : leaf true∉S) :
    ∃ w : V,m≠w ∧ C.Adj mid (.inl m) ∧ C.Adj (.inl m) (.inl w) ∧
      S={mid,.inl m,.inl w} := by
  obtain ⟨sz,c,hc,star⟩ := tile
  have only (x : V⊕Fin 3) (xs : x∈S) (e : C.Adj mid x) : x=.inl m := by
    rcases M x e with h|h|h
    · exact (lf (h ▸ xs)).elim
    · exact (dead (h ▸ xs)).elim
    · exact h
  have ne : c≠mid := by
    intro eq
    subst c
    have sub : S⊆{mid,.inl m} := by
      intro x hx
      by_cases same : x=mid
      · simp [same]
      · simp [only x hx (star x hx same)]
    have k := card_le_card sub
    rw [sz] at k
    simp [mid,card_insert_of_not_mem] at k
  have Cwire : C.Adj mid c := (star _ md (fun e=>ne e.symm)).symm
  have eq : c=.inl m := only c hc Cwire
  subst c
  obtain ⟨z,zs,zm,zc,shape⟩ := third sz md hc (by simp [mid])
  cases z with
  | inr k =>
    rcases tags (V:=V) k with e|e|e
    · exact (zm e).elim
    · exact (lf (e ▸ zs)).elim
    · exact (dead (e ▸ zs)).elim
  | inl w =>
    exact ⟨w,fun h=>zc (congrArg Sum.inl h.symm),Cwire,star _ zs zc,shape⟩

#print axioms shared_profile
#print axioms split_mid_profile
end
end KelmansCactus.AtomicBridge.ThetaDeadLeafProfiles
