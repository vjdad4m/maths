import SixTripleCutExceptionalEnd189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_three_nonsingleton_shores
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (cA : (G.induce (↑A : Set V)).Connected) (cB : (G.induce (↑B : Set V)).Connected)
    (cC : (G.induce (↑C : Set V)).Connected)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (a4 : 4≤A.card) (b4 : 4≤B.card) (c4 : 4≤C.card)
    {x : V} (xc : x∈C) (ux : ∀ t∈S,G.Adj x t) : False := by
  classical
  have va3 := shA.visible_lower ss conn (by omega)
  have vb3 := shB.visible_lower ss conn (by omega)
  obtain ⟨va,vb,insideC⟩ := universal_port_saturates_other_shores hc cap shC cC shA shB
    ac.symm bc.symm ab va3 vb3 xc ux
  have rankTwo {w : V}
      (no : (∀ t∈S,G.Adj w t) → False) : rank G S w≤2 := by
    by_contra! bad
    have une : ∀ t∈S,G.Adj w t := by
      intro t ts
      by_contra nt
      have b := rank_le_two_of_missing ss ts nt
      omega
    exact no une
  have ra (y : V) (ym : y∈A) : rank G S y≤2 :=
    rankTwo (fun uy=>no_two_universal_nonsingleton_shores hc cap conn degree ss
      shA shC shB cA cC ac ab bc.symm a4 c4 b4 ym xc uy ux)
  have rb (y : V) (ym : y∈B) : rank G S y≤2 :=
    rankTwo (fun uy=>no_two_universal_nonsingleton_shores hc cap conn degree ss
      shB shC shA cB cC bc ab.symm ac.symm b4 c4 a4 ym xc uy ux)
  have impossibleAt {W Z : Finset V} (shW : Shore G S W) (shZ : Shore G S Z)
      (cZ : (G.induce (↑Z : Set V)).Connected)
      (wz : Disjoint W Z) (wc : Disjoint W C) (zc : Disjoint Z C)
      (w4 : 4≤W.card) (z4 : 4≤Z.card)
      (vw : (visible G S W).card=3) (vz : (visible G S Z).card=3)
      (rw : ∀ y∈W,rank G S y≤2) (rz : ∀ y∈Z,rank G S y≤2)
      {t : V} (ts : t∈S) (bad : ¬ ∃ w∈ports G W t,6≤G.degree w) : False := by
    obtain ⟨l,lm,tl,low,_sole,good,qa,budget,_c6⟩ :=
      exceptional_port_geometry hc cap conn degree ss shW shZ shC wz wc zc w4 vw vz
        rw rz xc ux insideC ts bad
    have high {J : Finset V} (sep : Disjoint W J) : ∀ w∈J,6≤G.degree w := by
      intro w wm
      have nw : w≠l := fun e=>disjoint_left.mp sep lm (e ▸ wm)
      exact (degree w l nw).resolve_right (by omega)
    have eq := shore_card_of_universal_inside hc shC xc ux insideC ts
    obtain ⟨y,yt,u,us,ut,yu⟩ := exceptional_other_port_rank_two hc cap conn ss
      shW shZ shC wz wc zc z4 c4 vz (high wz) lm tl ts ux eq qa
    obtain ⟨z,zu,zh⟩ := good u us ut
    exact no_exceptional_two_terminal_port hc cap ss shW shZ shC cZ wz wc zc z4 c4
      vw vz (high wz) (high wc) rw ux insideC lm tl low yt
      (mem_filter.mpr ⟨(mem_filter.mp yt).1,yu.symm⟩) zu zh ts us ut budget
  have ag (t : V) (ts : t∈S) : ∃ w∈ports G A t,6≤G.degree w := by
    by_contra no
    exact impossibleAt shA shB cB ab ac bc a4 b4 va vb ra rb ts no
  have bg (t : V) (ts : t∈S) : ∃ w∈ports G B t,6≤G.degree w := by
    by_contra no
    exact impossibleAt shB shA cA ab.symm bc ac b4 a4 vb va rb ra ts no
  exact no_three_shores_with_high_port_of_universal hc cap conn ss shA shB shC cC
    ab ac bc a4 b4 c4 ag bg ra rb xc ux

/-- Any actual three-vertex separator under the degree-six Graffiti
hypotheses in a three-connected graph has at most two components. -/
theorem three_cut_at_most_two_components
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) :
    Nat.card (Removed G S).ConnectedComponent≤2 := by
  classical
  by_contra! big
  let C := (Removed G S).ConnectedComponent
  letI : Finite C := Finite.of_surjective (Removed G S).connectedComponentMk (fun y=>y.exists_rep)
  letI : Fintype C := Fintype.ofFinite C
  have c : 3≤Fintype.card C := by
    change 2<Nat.card C at big
    rw [Nat.card_eq_fintype_card] at big
    omega
  let f : Fin 3 ↪ C := (Fin.castLEEmb c).trans (Fintype.equivFin C).symm.toEmbedding
  let A (i : Fin 3) := shoreSet (f i)
  have sh (i : Fin 3) : Shore G S (A i) := shoreSet_shore (f i)
  have co (i : Fin 3) : (G.induce (↑(A i) : Set V)).Connected := shoreSet_connected (f i)
  have dis : Pairwise fun i j=>Disjoint (A i) (A j) :=
    fun _ _ ne=>shoreSet_disjoint (f.injective.ne ne)
  have a4 (i : Fin 3) : 4≤(A i).card := by
    have pos := card_pos.mpr (sh i).nonempty
    have no : (A i).card≠1 := by
      intro h
      have h' := three_cut_at_most_two_with_singleton hc cap conn degree ss (X:=f i) h
      change Nat.card C ≤ 2 at h'
      rw [Nat.card_eq_fintype_card] at h'
      omega
    obtain ⟨a,am,b,bm,ne⟩ := one_lt_card.mp (by omega : 1<(A i).card)
    have l := (sh i).degree_bound am
    have k := (sh i).degree_bound bm
    rw [ss] at l k
    rcases degree a b ne with h|h <;> omega
  obtain ⟨i,x,xm,un⟩ := universal_port_of_three_shores hc cap conn degree ss A sh co dis
  obtain ⟨j,k,ij,ik,jk⟩ :=
    (show ∀ i : Fin 3,∃ j k : Fin 3,i≠j ∧ i≠k ∧ j≠k by decide) i
  exact no_three_nonsingleton_shores hc cap conn degree ss (sh j) (sh k) (sh i)
    (co j) (co k) (co i) (dis jk) (dis ij.symm) (dis ik.symm) (a4 j) (a4 k) (a4 i) xm un

#print axioms no_three_nonsingleton_shores
#print axioms three_cut_at_most_two_components
end Graffiti189LongestPath.ThresholdSix.ThreeCut
