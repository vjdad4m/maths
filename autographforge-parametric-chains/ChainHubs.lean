import GraphResidue

namespace TwinForcing
open SimpleGraph Finset

/-- Right hub of block i is joined to the left hub of block i+1; optional
spines join the two hubs in each block. -/
def chainHubAdj {n : ℕ} (spine : Bool) (x y : Fin n × Bool) : Prop :=
  (spine = true ∧ x.1 = y.1 ∧ x.2 ≠ y.2) ∨
  (x.2 = true ∧ y.2 = false ∧ x.1.val + 1 = y.1.val) ∨
  (x.2 = false ∧ y.2 = true ∧ y.1.val + 1 = x.1.val)

def chainHubs (n : ℕ) (spine : Bool) : SimpleGraph (Fin n × Bool) where
  Adj := chainHubAdj spine
  symm := by
    intro x y e
    rcases e with ⟨s,i,b⟩|⟨b,c,i⟩|⟨b,c,i⟩
    · exact Or.inl ⟨s,i.symm,Ne.symm b⟩
    · exact Or.inr (Or.inr ⟨c,b,i⟩)
    · exact Or.inr (Or.inl ⟨c,b,i⟩)
  loopless := by
    intro x e
    rcases e with ⟨_,_,b⟩|⟨_,_,i⟩|⟨_,_,i⟩
    · exact b rfl
    · omega
    · omega

instance (n : ℕ) (spine : Bool) : DecidableRel (chainHubs n spine).Adj :=
  fun x y => by change Decidable (chainHubAdj spine x y); unfold chainHubAdj; infer_instance

private theorem left_neighbors {n : ℕ} (spine : Bool) (i : Fin n) :
    (chainHubs n spine).neighborFinset (i,false) =
      (if spine then {(i,true)} else ∅) ∪
        (if h : 0 < i.val then {(⟨i.val-1,by omega⟩,true)} else ∅) := by
  ext ⟨j,b⟩
  rw [mem_neighborFinset]
  change chainHubAdj spine (i,false) (j,b) ↔ _
  cases spine <;> cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split_ifs <;>
    simp [chainHubAdj, Prod.mk.injEq, Fin.ext_iff] <;> omega

private theorem right_neighbors {n : ℕ} (spine : Bool) (i : Fin n) :
    (chainHubs n spine).neighborFinset (i,true) =
      (if spine then {(i,false)} else ∅) ∪
        (if h : i.val+1 < n then {(⟨i.val+1,h⟩,false)} else ∅) := by
  ext ⟨j,b⟩
  rw [mem_neighborFinset]
  change chainHubAdj spine (i,true) (j,b) ↔ _
  cases spine <;> cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split_ifs <;>
    simp [chainHubAdj, Prod.mk.injEq, Fin.ext_iff] <;> omega

theorem chain_left_degree {n : ℕ} (spine : Bool) (i : Fin n) :
    (chainHubs n spine).degree (i,false) = spine.toNat + (if 0 < i.val then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree,left_neighbors]
  cases spine <;> simp only [Bool.false_eq_true,if_false,if_true] <;> split_ifs with h <;> simp
  rw [← Finset.insert_eq, Finset.card_pair]
  intro e
  have e' := congrArg (fun x : Fin n × Bool => x.1.val) e
  simp only at e'
  omega

theorem chain_right_degree {n : ℕ} (spine : Bool) (i : Fin n) :
    (chainHubs n spine).degree (i,true) = spine.toNat + (if i.val+1 < n then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree,right_neighbors]
  cases spine <;> simp only [Bool.false_eq_true,if_false,if_true] <;> split_ifs with h <;> simp
  rw [← Finset.insert_eq, Finset.card_pair]
  intro e
  have e' := congrArg (fun x : Fin n × Bool => x.1.val) e
  simp only at e'
  omega


theorem chain_hub_bag (j : ℕ) (spine : Bool) :
    degreeBag (chainHubs (j+3) spine) =
      ((List.replicate (2*j+4) (spine.toNat+1) ++
         List.replicate 2 spine.toNat : List ℕ) : Multiset ℕ) := by
  let x : Fin (j+3) × Bool := (0,false)
  let y : Fin (j+3) × Bool := (⟨j+2,by omega⟩,true)
  let S : Finset (Fin (j+3) × Bool) := (univ.erase x).erase y
  have ne : y ≠ x := by simp [x,y]
  have hxy : y ∈ (univ : Finset (Fin (j+3) × Bool)).erase x :=
    mem_erase.mpr ⟨ne,mem_univ _⟩
  have hy : y ∉ S := not_mem_erase _ _
  have hx : x ∉ insert y S := by simp [S,ne.symm]
  have decomp : insert x (insert y S) = univ := by simp [S,hxy]
  have size : S.card = 2*j+4 := by
    simp only [S,card_erase_of_mem hxy,card_erase_of_mem (mem_univ x),
      card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  let d := fun v : Fin (j+3) × Bool => (chainHubs (j+3) spine).degree v
  have dx : d x = spine.toNat := by
    change (chainHubs (j+3) spine).degree (0,false) = _
    rw [chain_left_degree]
    simp
  have dy : d y = spine.toNat := by
    change (chainHubs (j+3) spine).degree (⟨j+2,by omega⟩,true) = _
    rw [chain_right_degree]
    simp
  have middle : ∀ v ∈ S, d v = spine.toNat + 1 := by
    rintro ⟨i,b⟩ hv
    have nx := (mem_erase.mp (mem_erase.mp hv).2).1
    have ny := (mem_erase.mp hv).1
    cases b
    · change (chainHubs (j+3) spine).degree (i,false) = _
      have hi : 0 < i.val := by
        apply Classical.byContradiction
        intro e
        apply nx
        exact Prod.ext (Fin.ext (by change i.val = 0; omega)) rfl
      rw [chain_left_degree,if_pos hi]
    · change (chainHubs (j+3) spine).degree (i,true) = _
      have hi : i.val+1 < j+3 := by
        apply Classical.byContradiction
        intro e
        apply ny
        have := i.isLt
        exact Prod.ext (Fin.ext (by change i.val = j+2; omega)) rfl
      rw [chain_right_degree,if_pos hi]
  have hs : S.val.map d = Multiset.replicate (2*j+4) (spine.toNat+1) := by
    rw [Multiset.map_congr rfl (fun a ha => middle a ha),Multiset.map_const',← card_def,size]
  change (univ : Finset (Fin (j+3) × Bool)).val.map d = _
  rw [← decomp]
  rw [Finset.insert_val_of_not_mem hx,Finset.insert_val_of_not_mem hy]
  rw [Multiset.map_cons,Multiset.map_cons,dx,dy,hs]
  change _ = Multiset.replicate (2*j+4) (spine.toNat+1) + Multiset.replicate 2 spine.toNat
  exact (show _ = Multiset.replicate 2 spine.toNat +
      Multiset.replicate (2*j+4) (spine.toNat+1) by
        simp only [show (2 : ℕ) = 0+1+1 by decide, Multiset.replicate_succ,
          Multiset.replicate_zero, Multiset.cons_add, zero_add]).trans (add_comm _ _)

abbrev chainGraph (n m : ℕ) (spine : Bool) := @pageGraph n m (chainHubs n spine)

theorem fan_chain_forcing_excess (j : ℕ) :
    StarCone.forcing (chainGraph (j+3) (4*j+9) false) 2 =
      graphResidue (chainGraph (j+3) (4*j+9) false) + (2*j*j+8*j+7) :=
  fan_forcing_excess j _ (chain_hub_bag j false)

theorem book_chain_forcing_excess (j : ℕ) :
    StarCone.forcing (chainGraph (j+3) (4*j+9) true) 2 =
      graphResidue (chainGraph (j+3) (4*j+9) true) + (2*j*j+7*j+4) :=
  book_forcing_excess j _ (chain_hub_bag j true)

#print axioms chain_hub_bag
#print axioms fan_chain_forcing_excess
#print axioms book_chain_forcing_excess
end TwinForcing
