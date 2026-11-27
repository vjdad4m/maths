import ComponentPorts180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 500000
namespace Minimal180.PairRepair.Nine
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
abbrev V := Fin 9
noncomputable def E : List (V×V) := [(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,6),(1,7),(2,3),(2,8),(4,5),(4,6),(5,7)]
noncomputable def G : SimpleGraph V where
  Adj x y := x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl
noncomputable instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)))
noncomputable abbrev A : Finset V := {0,6,7}
noncomputable abbrev P : Finset V := {0,2,3,5,6,7}
noncomputable abbrev C : Finset V := {2,3,8}
noncomputable abbrev D : Finset V := {4,5,6,7}
noncomputable def d (x : V) := ([2,1,2,2,1,2,0,2,3]:List ℕ)[x.val]!

theorem data : G.Connected ∧ parity G 6 false=P ∧ Indep G A ∧ eligible A P 6=P ∧ A∩insert 6 P=A := by
  have ⟨gc,dist⟩ : G.Connected ∧ ∀ x,G.dist x 6=d x := by
    apply layers
    · exact (by decide : d 6=0)
    · intro x y
      exact (show ∀ i j : V,G.Adj i j → d i≤d j+1 by decide) x y
    · exact (show ∀ x : V,x≠6 → ∃ y,G.Adj x y ∧ d x=d y+1 by decide)
  exact ⟨gc,by ext x;simp only [mem_parity,dist];exact (show ∀ v : V,d v%2=false.toNat ↔ v∈P by decide) x,
    by unfold Indep;decide,by decide,by decide⟩

theorem transversal : TwoColor G (univ\({0,1}:Finset V)) :=
  ⟨{2,4,7},{3,5,6,8},by decide,by decide,by unfold Indep;decide,by unfold Indep;decide⟩

theorem three_deletions : TwoColor G (univ\({1,2,4}:Finset V)) :=
  ⟨{0,6,7,8},{3,5},by decide,by decide,by unfold Indep;decide,by unfold Indep;decide⟩

theorem leaves : weightedLeaves G P=4 := by
  let J : Finset V := {0,1,2}
  have co : Con G J := by
    have start := con_insert G (con_single G (2:V)) (mem_singleton_self _) (by decide : G.Adj 1 2)
    exact con_insert G start (show (2:V)∈({1,2}:Finset V) by decide) (by decide : G.Adj 0 2)
  have low := weightedCore G J P co (by dsimp [J,Dominates];decide)
  have val : (P\J).card=4 := by decide
  rw [val] at low
  obtain ⟨T,sub,tr,opt⟩ := tree_opt G data.1 P
  let L := P∩Graffiti177.leaves T
  have ct : L.card=weightedLeaves G P := opt
  by_contra neq
  have lp : L⊆P := inter_subset_left
  have count : P.card=6 := by decide
  have miss : (P\L).card≤1 := by have := card_sdiff_add_card_eq_card lp;omega
  have core := (leaf_core G T sub tr (by decide) L inter_subset_right).1
  have iso (u : V) (up : u∉P) (u1 : u≠1) (allN : G.neighborFinset u⊆L) : False := by
    have um : u∈univ\L := mem_sdiff.mpr ⟨mem_univ _,fun m => up (lp m)⟩
    have om : (1:V)∈univ\L := mem_sdiff.mpr ⟨mem_univ _,fun m => (by decide : (1:V)∉P) (lp m)⟩
    have no (z : V) (zm : z∈univ\L) (ed : G.Adj u z) : False :=
      (mem_sdiff.mp zm).2 (allN ((G.mem_neighborFinset u z).mpr ed))
    have stable : OnEdges G (univ\L) (fun x => decide (x=u)) := by
      intro x xm y ym ed
      have nx : x≠u := fun eq => no y ym (eq ▸ ed)
      have ny : y≠u := fun eq => no x xm (eq ▸ ed.symm)
      simp [nx,ny]
    have eq := ((connected_cuts G _).mp core).2 _ stable u um 1 om
    simp [u1.symm] at eq
  have two : (2:V)∉L := by
    intro h
    apply iso 8 (by decide) (by decide)
    rw [show G.neighborFinset 8=({2}:Finset V) by decide]
    exact singleton_subset_iff.mpr h
  have rest (v : V) (vp : v∈P) (ne : v≠2) : v∈L := by
    by_contra off
    have inc : ({v,2}:Finset V)⊆P\L := insert_subset (mem_sdiff.mpr ⟨vp,off⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨by decide,two⟩))
    have n := card_le_card inc
    rw [card_pair ne] at n;omega
  apply iso 4 (by decide) (by decide)
  rw [show G.neighborFinset 4=({0,5,6}:Finset V) by decide]
  exact insert_subset (rest 0 (by decide) (by decide)) (insert_subset (rest 5 (by decide) (by decide))
    (singleton_subset_iff.mpr (rest 6 (by decide) (by decide))))

theorem budget : allowance G 6 false A=3 := by
  obtain ⟨gc,par,ai,el,_⟩ := data
  have id := allowance_eq G gc (by decide) 6 false A ai
  dsimp only at id;rw [par,el,leaves] at id
  have n : Fintype.card V=9 := by decide
  have ac : A.card=3 := by decide
  have pc : P.card=6 := by decide
  omega

#print axioms data
#print axioms leaves
#print axioms budget
end Minimal180.PairRepair.Nine
