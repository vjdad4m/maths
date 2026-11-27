import MinimalAtomCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open ThreePort FourRingCutAux
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

instance capDecAdj (A : Finset V) (p : Fin 3→V) : DecidableRel (atomCap G A p).Adj :=
  Classical.decRel _

private def nbrOld {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q)
    (a : ↑A) (b : G.neighborSet a.val) :
    (atomCap G A p).neighborSet (.inl a) := by
  classical
  by_cases bA : b.val∈A
  · exact ⟨.inl ⟨b.val,bA⟩,b.property⟩
  · have e := (S.edge _ a.property _ bA).mp b.property
    exact ⟨capRoot A,e.imp (fun _ h=>h.1)⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem nbrOld_pos {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q)
    (a : ↑A) (b : G.neighborSet a.val) (bA : b.val∈A) :
    (nbrOld S a b).val=Sum.inl ⟨b.val,bA⟩ := by simp [nbrOld,bA]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem nbrOld_neg {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q)
    (a : ↑A) (b : G.neighborSet a.val) (bA : b.val∉A) :
    (nbrOld S a b).val=capRoot A := by simp [nbrOld,bA]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem nbrOld_bij {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q)
    (a : ↑A) : Function.Bijective (nbrOld S a) := by
  constructor
  · intro b c eq
    apply Subtype.ext
    have ce := congrArg Subtype.val eq
    by_cases bA : b.val∈A <;> by_cases cA : c.val∈A
    · rw [nbrOld_pos S _ _ bA,nbrOld_pos S _ _ cA] at ce
      exact congrArg (fun t : ↑A=>t.val) (Sum.inl.inj ce)
    · rw [nbrOld_pos S _ _ bA,nbrOld_neg S _ _ cA] at ce
      cases ce
    · rw [nbrOld_neg S _ _ bA,nbrOld_pos S _ _ cA] at ce
      cases ce
    · obtain ⟨i,e,bi⟩ := (S.edge _ a.property _ bA).mp b.property
      obtain ⟨j,f,cj⟩ := (S.edge _ a.property _ cA).mp c.property
      have same := S.left_inj (e.trans f.symm)
      exact bi.symm.trans (same ▸ cj)
  · rintro ⟨⟨b,bA⟩|u,h⟩
    · let y : G.neighborSet a.val := ⟨b,h⟩
      exact ⟨y,Subtype.ext (nbrOld_pos S _ _ bA)⟩
    · cases u
      obtain ⟨i,ai⟩ := h
      have e := (S.edge _ a.property _ (S.right i)).mpr ⟨i,ai,rfl⟩
      let y : G.neighborSet a.val := ⟨q i,e⟩
      exact ⟨y,Subtype.ext (nbrOld_neg S _ _ (S.right i))⟩

private def atRoot {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q)
    (i : Fin 3) : (atomCap G A p).neighborSet (capRoot A) :=
  ⟨.inl ⟨p i,S.left i⟩,⟨i,rfl⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem atRoot_bij {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q) :
    Function.Bijective (atRoot S) := by
  constructor
  · intro i j eq
    have h := congrArg Subtype.val eq
    have same : (Sum.inl ⟨p i,S.left i⟩ : CapV A)=Sum.inl ⟨p j,S.left j⟩ := h
    exact S.left_inj (congrArg Subtype.val (Sum.inl.inj same))
  · rintro ⟨⟨a,aA⟩|nil,h⟩
    · obtain ⟨i,ia⟩ := h
      refine ⟨i,Subtype.ext ?_⟩
      exact congrArg Sum.inl (Subtype.ext ia)
    · exact h.elim

/-- Capping a three-edge matching seam preserves cubicity, including
at the new root. -/
theorem atom_cap_cubic (cub : ∀a,G.degree a=3)
    {A : Finset V} {p q : Fin 3→V} (S : Seam (G:=G) A p q) :
    ∀ a,(atomCap G A p).degree a=3 := by
  rintro (a|u)
  · have he := Fintype.card_congr (Equiv.ofBijective _ (nbrOld_bij S a))
    rw [card_neighborSet_eq_degree,card_neighborSet_eq_degree,cub] at he
    exact he.symm
  · cases u
    have he := Fintype.card_congr (Equiv.ofBijective _ (atRoot_bij S))
    rw [card_neighborSet_eq_degree,Fintype.card_fin] at he
    exact he.symm

/-- Capped minimal shores are cubic cyclic-four atoms and retain
3-vertex-connectivity. -/
theorem minimal_atom_cap_domain (cub : ∀a,G.degree a=3)
    (minimum : MinBoundaryThree G) {A : Finset V} (ma : MinimalShore G A)
    {p q : Fin 3→V} (S : Seam (G:=G) A p q) :
    (∀ a,(atomCap G A p).degree a=3) ∧
    KelmansStarter.ThreeConnected (atomCap G A p) ∧ SmallTrivial (atomCap G A p) := by
  classical
  have capC := atom_cap_cubic cub S
  have small := minimal_shore_cap_small minimum ma S
  have four : 4≤Fintype.card (CapV A) := by
    let r := capRoot A
    let H := atomCap G A p
    have off : H.neighborFinset r ⊆ (univ:Finset (CapV A)).erase r := by
      intro x h
      exact mem_erase.mpr ⟨((H.mem_neighborFinset _ _).mp h).ne.symm,mem_univ _⟩
    have bound := card_le_card off
    rw [card_neighborFinset_eq_degree,card_erase_of_mem (mem_univ r),card_univ] at bound
    change (atomCap G A p).degree r≤_ at bound
    rw [capC] at bound
    omega
  exact ⟨capC,three_connected_of_small_trivial _ capC four small,small⟩

#print axioms minimal_atom_cap_domain
end
end KelmansCactus.AtomicBridge.OddUncross
