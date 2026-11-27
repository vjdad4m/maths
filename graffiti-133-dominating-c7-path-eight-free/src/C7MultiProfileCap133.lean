import C7MultiSmallScopes133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133MultiC7
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

private lemma trans_inj : ∀ r a b : Fin 7, r+a=r+b → a=b := by decide
private lemma trans_sur : ∀ r b : Fin 7, ∃ a, r+a=b := by decide
private lemma trans_cycle : ∀ r a b : Fin 7, Cyclic (r+a) (r+b) ↔ Cyclic a b := by decide
private lemma offset_63 : ∀ i : Fin 7, (i+6)+3=i+2 := by decide
private lemma offset_13 : ∀ i : Fin 7, (i+1)+3=i+4 := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An adjacent two-contact profile cannot coexist with the two indicated
distance-three profiles in an ordinary-C4-free induced-P8-free graph. -/
theorem forbid_adjacent_far_far (H : Hole G 7) (h4 : FourCycleFree G)
    (h8 : ¬∃ p : Fin 8 → V, InducedPath G p) (i : Fin 7) {x y z : V}
    (hx : Outside H.c x) (hy : Outside H.c y) (hz : Outside H.c z)
    (ax : contactSet H x={i,i+1}) (ay : contactSet H y={i+1,i+4})
    (az : contactSet H z={i+6,i+2}) : False := by
  classical
  let C (j : Fin 7) := H.c (i+j)
  have ci : Function.Injective C := fun _ _ e => trans_inj i _ _ (H.inj e)
  have ce (a b : Fin 7) : G.Adj (C a) (C b) ↔ Cyclic a b :=
    (H.adj _ _).trans (trans_cycle i a b)
  have offx (j : Fin 7) : x≠C j := hx (i+j)
  have offy (j : Fin 7) : y≠C j := hy (i+j)
  have offz (j : Fin 7) : z≠C j := hz (i+j)
  have ex (j : Fin 7) : G.Adj x (C j) ↔ j=0 ∨ j=1 := by
    change G.Adj x (H.c (i+j)) ↔ _
    rw [←mem_contactSet,ax,Finset.mem_insert,Finset.mem_singleton]
    have e₀ : i+j=i ↔ j=0 := by
      have e : i+j=i+0 ↔ j=0 := ⟨trans_inj i _ _,congrArg (i+·)⟩
      rw [add_zero] at e
      exact e
    have e₁ : i+j=i+1 ↔ j=1 := ⟨trans_inj i _ _,congrArg (i+·)⟩
    rw [e₀,e₁]
  have ey (j : Fin 7) : G.Adj y (C j) ↔ j=1 ∨ j=4 := by
    change G.Adj y (H.c (i+j)) ↔ _
    rw [←mem_contactSet,ay,Finset.mem_insert,Finset.mem_singleton]
    have e₁ : i+j=i+1 ↔ j=1 := ⟨trans_inj i _ _,congrArg (i+·)⟩
    have e₄ : i+j=i+4 ↔ j=4 := ⟨trans_inj i _ _,congrArg (i+·)⟩
    rw [e₁,e₄]
  have ez (j : Fin 7) : G.Adj z (C j) ↔ j=6 ∨ j=2 := by
    change G.Adj z (H.c (i+j)) ↔ _
    rw [←mem_contactSet,az,Finset.mem_insert,Finset.mem_singleton]
    have e₆ : i+j=i+6 ↔ j=6 := ⟨trans_inj i _ _,congrArg (i+·)⟩
    have e₂ : i+j=i+2 ↔ j=2 := ⟨trans_inj i _ _,congrArg (i+·)⟩
    rw [e₆,e₂]
  have nxy : ¬G.Adj x y := by
    intro e
    have h := h4 (C 0) y (C 1) x (offy 0).symm
      ((ce 0 1).mpr (by decide)) ((ey 1).mpr (Or.inl rfl)) ((ex 0).mpr (Or.inl rfl)).symm e.symm
    exact offx 1 h.symm
  have nxz : ¬G.Adj x z := by
    intro e
    have h := h4 (C 0) z (C 6) x (offz 0).symm
      ((ce 0 6).mpr (by decide)) ((ez 6).mpr (Or.inl rfl)) ((ex 0).mpr (Or.inl rfl)).symm e.symm
    exact offx 6 h.symm
  have nyz : ¬G.Adj y z := by
    intro e
    have h := h4 (C 1) z (C 2) y (offz 1).symm
      ((ce 1 2).mpr (by decide)) ((ez 2).mpr (Or.inr rfl)) ((ey 1).mpr (Or.inl rfl)).symm e.symm
    exact offy 2 h.symm
  have xy : x≠y := by
    intro e
    have h := (ex 0).mpr (Or.inl rfl)
    rw [e,ey] at h
    exact (by decide : ¬((0:Fin 7)=1 ∨ (0:Fin 7)=4)) h
  have xz : x≠z := by
    intro e
    have h := (ex 0).mpr (Or.inl rfl)
    rw [e,ez] at h
    exact (by decide : ¬((0:Fin 7)=6 ∨ (0:Fin 7)=2)) h
  have yz : y≠z := by
    intro e
    have h := (ey 1).mpr (Or.inl rfl)
    rw [e,ez] at h
    exact (by decide : ¬((1:Fin 7)=6 ∨ (1:Fin 7)=2)) h
  let p : Fin 8 → V := ![x,C 0,C 6,z,C 2,C 3,C 4,y]
  have inj : Function.Injective p := List.nodup_ofFn.mp (by
    simpa [p,List.ofFn_succ] using (show [x,C 0,C 6,z,C 2,C 3,C 4,y].Nodup by
      simp [xy,xz,yz,yz.symm,offx,offy,offz,Ne.symm,ci.eq_iff]))
  refine h8 ⟨p,inj,?_⟩
  intro a b lt
  have ex' (j) : G.Adj (C j) x ↔ j=0 ∨ j=1 := (G.adj_comm _ _).trans (ex j)
  have ey' (j) : G.Adj (C j) y ↔ j=1 ∨ j=4 := (G.adj_comm _ _).trans (ey j)
  have ez' (j) : G.Adj (C j) z ↔ j=6 ∨ j=2 := (G.adj_comm _ _).trans (ez j)
  have nyx : ¬G.Adj y x := fun e => nxy e.symm
  have nzx : ¬G.Adj z x := fun e => nxz e.symm
  have nzy : ¬G.Adj z y := fun e => nyz e.symm
  fin_cases a <;> fin_cases b <;>
    first | (exfalso; exact (by decide : ¬(_ < _)) lt)
          | (simp [p,ce,Cyclic,ex,ey,ez,ex',ey',ez',nxy,nxz,nyz,nyx,nzx,nzy,G.loopless] <;> decide)

private lemma preimage_translation_card (M : Finset (Fin 7)) (r : Fin 7) :
    (Finset.univ.filter fun i => r+i∈M).card=M.card := by
  apply Finset.card_bij (fun a _ => r+a)
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a _ b _ e
    exact trans_inj r _ _ e
  · intro b hb
    obtain ⟨a,ea⟩ := trans_sur r b
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ea.symm ▸ hb⟩,ea⟩

/-- The cyclic missing-profile argument, independent of the graph. -/
theorem weighted_profile_cap (A F : Finset (Fin 7))
    (noTrip : ∀ i∈A, i+1∈F → i+6∈F → False) : A.card+2*F.card≤14 := by
  let M := Finset.univ \ F
  let U := Finset.univ.filter fun i => (1:Fin 7)+i∈M
  let W := Finset.univ.filter fun i => (6:Fin 7)+i∈M
  have subset : A⊆U∪W := by
    intro j hj
    by_cases a : j+1∈F <;> by_cases b : j+6∈F
    · exact (noTrip j hj a b).elim
    · exact Finset.mem_union.mpr (Or.inr (by simp [W,M,add_comm (6:Fin 7) j,b]))
    · exact Finset.mem_union.mpr (Or.inl (by simp [U,M,add_comm (1:Fin 7) j,a]))
    · exact Finset.mem_union.mpr (Or.inl (by simp [U,M,add_comm (1:Fin 7) j,a]))
  have uc : U.card=M.card := preimage_translation_card M 1
  have wc : W.card=M.card := preimage_translation_card M 6
  have sum : M.card+F.card=7 := by
    simpa [M] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
  have h := (Finset.card_le_card subset).trans (Finset.card_union_le U W)
  omega

noncomputable def adjacentPairSites (H : Hole G 7) : Finset (Fin 7) := by
  classical exact Finset.univ.filter fun i => ∃ x, Outside H.c x ∧ contactSet H x={i,i+1}

noncomputable def farPairSites (H : Hole G 7) : Finset (Fin 7) := by
  classical exact Finset.univ.filter fun i => ∃ x, Outside H.c x ∧ contactSet H x={i,i+3}

theorem pair_profile_weight_cap (H : Hole G 7) (h4 : FourCycleFree G)
    (h8 : ¬∃ p : Fin 8 → V, InducedPath G p) :
    (adjacentPairSites H).card+2*(farPairSites H).card≤14 := by
  classical
  apply weighted_profile_cap
  intro i a b c
  obtain ⟨x,hx,ax⟩ := (Finset.mem_filter.mp a).2
  obtain ⟨y,hy,ay⟩ := (Finset.mem_filter.mp b).2
  obtain ⟨z,hz,az⟩ := (Finset.mem_filter.mp c).2
  rw [offset_13] at ay
  rw [offset_63] at az
  exact forbid_adjacent_far_far H h4 h8 i hx hy hz ax ay az

private theorem vertex_profiles_inject_into_sites (H : Hole G 7) (h4 : FourCycleFree G)
    (U : Finset V) (k : Fin 7) (nonzero : ∀ i : Fin 7, i≠i+k)
    (p : ∀ x∈U, Outside H.c x ∧ ∃ i, contactSet H x={i,i+k}) :
    U.card ≤ (Finset.univ.filter fun i => ∃ x, Outside H.c x ∧ contactSet H x={i,i+k}).card := by
  classical
  let label (x : V) := if h : x∈U then Classical.choose (p x h).2 else 0
  have spec (x : V) (hx : x∈U) : contactSet H x={label x,label x+k} := by
    rw [show label x=Classical.choose (p x hx).2 from dif_pos hx]
    exact Classical.choose_spec (p x hx).2
  refine Finset.card_le_card_of_injOn label ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,(p x hx).1,spec x hx⟩
  · intro x hx y hy eq
    by_contra ne
    have cap := disjoint_contact_pairs H h4 ne
    change x∈U at hx
    change y∈U at hy
    rw [spec x hx,spec y hy,eq,Finset.inter_self,Finset.card_pair (nonzero _)] at cap
    omega

/-- Vertex-count form of the weighted profile budget, for any selected
subsets of adjacent- and distance-three two-contact exterior vertices. -/
theorem pair_vertex_weight_cap (H : Hole G 7) (h4 : FourCycleFree G)
    (h8 : ¬∃ p : Fin 8 → V, InducedPath G p) (A F : Finset V)
    (ha : ∀ x∈A, Outside H.c x ∧ ∃ i, contactSet H x={i,i+1})
    (hf : ∀ x∈F, Outside H.c x ∧ ∃ i, contactSet H x={i,i+3}) :
    A.card+2*F.card≤14 := by
  classical
  have a : A.card≤(adjacentPairSites H).card := vertex_profiles_inject_into_sites H h4 A 1 (by decide) ha
  have f : F.card≤(farPairSites H).card := vertex_profiles_inject_into_sites H h4 F 3 (by decide) hf
  have e := pair_profile_weight_cap H h4 h8
  omega

#print axioms forbid_adjacent_far_far
#print axioms weighted_profile_cap
#print axioms pair_profile_weight_cap
#print axioms pair_vertex_weight_cap
end Graffiti133MultiC7
