import ActiveContacts180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 500000
namespace Minimal180.PairRepair.Tight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
abbrev V := Fin 9
noncomputable def E : List (V×V) := [(0,8),(0,4),(0,5),(0,6),(1,5),(1,7),(2,6),(2,7),(3,8),(3,7),(4,8),(5,6),(7,8)]
noncomputable def G : SimpleGraph V where
  Adj x y := x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl
noncomputable instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)))
noncomputable abbrev A : Finset V := {0,1,2,3}
noncomputable abbrev P : Finset V := {0,1,2,3,6,8}
noncomputable abbrev C : Finset V := {1,2,5,6}
noncomputable abbrev D : Finset V := {3,4,8}
noncomputable def d (x : V) := ([2,0,2,2,3,1,2,1,2]:List ℕ)[x.val]!
noncomputable def paint (x : V) : Bool := decide (x∈({2,5,8}:Finset V))

theorem data : G.Connected ∧ parity G 1 false=P ∧ Indep G A ∧ eligible A P 1=P ∧ A∩insert 1 P=A := by
  have ⟨gc,dist⟩ : G.Connected ∧ ∀ x,G.dist x 1=d x := by
    apply layers
    · exact (by decide : d 1=0)
    · intro x y
      exact (show ∀ i j : V,G.Adj i j → d i≤d j+1 by decide) x y
    · exact (show ∀ x : V,x≠1 → ∃ y,G.Adj x y ∧ d x=d y+1 by decide)
  exact ⟨gc,by ext x;simp only [mem_parity,dist];exact (show ∀ v : V,d v%2=false.toNat ↔ v∈P by decide) x,
    by unfold Indep;decide,by decide,by decide⟩

noncomputable def cutColor (x v : V) : Bool := decide (v∈(([
    {0,4,5},{1,5,7},{2,7},{3,7},∅,∅,{4},∅,{8,4,7}]:List (Finset V))[x.val]!))

theorem leaves : weightedLeaves G P=4 := by
  let J : Finset V := {0,7,8}
  have co : Con G J := by
    have start := con_insert G (con_single G (8:V)) (mem_singleton_self _) (by decide : G.Adj 7 8)
    exact con_insert G start (show (8:V)∈({7,8}:Finset V) by decide) (by decide : G.Adj 0 8)
  have lo := weightedCore G J P co (by dsimp [J,Dominates];decide)
  rw [show (P\J).card=4 by decide] at lo
  obtain ⟨T,sub,tr,opt⟩ := tree_opt G data.1 P
  by_contra neq
  obtain ⟨L,inc,five⟩ := exists_subset_card_eq (show 5≤(P∩Graffiti177.leaves T).card by omega)
  have lp : L⊆P := inc.trans inter_subset_left
  have size := card_sdiff_add_card_eq_card lp
  rw [five,show P.card=6 by decide] at size
  obtain ⟨x,one⟩ := Finset.card_eq_one.mp (show (P\L).card=1 by omega)
  have xp : x∈P := (mem_sdiff.mp (show x∈P\L from one ▸ mem_singleton_self _)).1
  have lx : L=P.erase x := by
    ext v
    have rel := Finset.ext_iff.mp one v
    have inP := fun (h:v∈L) => lp h
    simp only [mem_sdiff,mem_singleton] at rel
    simp only [mem_erase]
    constructor
    · intro vl
      exact ⟨fun eq => (rel.mpr eq).2 vl,inP vl⟩
    · rintro ⟨ne,vm⟩
      exact Classical.byContradiction (fun miss => ne (rel.mp ⟨vm,miss⟩))
  have con := (leaf_core G T sub tr (by decide) L (inc.trans inter_subset_right)).1
  rw [lx] at con
  have check := (show ∀ x∈P,OnEdges G (univ\P.erase x) (cutColor x) ∧
    ¬ConstantOn (univ\P.erase x) (cutColor x) by unfold OnEdges ConstantOn;decide) x xp
  exact check.2 (((connected_cuts G _).mp con).2 _ check.1)

theorem budget : allowance G 1 false A=2 := by
  obtain ⟨gc,par,ai,el,_⟩ := data
  have id := allowance_eq G gc (by decide) 1 false A ai
  dsimp only at id;rw [par,el,leaves] at id
  have n : Fintype.card V=9 := by decide
  have ac : A.card=4 := by decide
  have pc : P.card=6 := by decide
  omega

#print axioms data
#print axioms leaves
#print axioms budget
end Minimal180.PairRepair.Tight
