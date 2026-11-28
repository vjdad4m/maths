import SixTripleCutBasics189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem sum_cards_le {I : Type*} [DecidableEq I] (T : Finset I)
    (F : I→Finset V) (dis : Pairwise fun i j => Disjoint (F i) (F j))
    {B : Finset V} (incl : ∀ i∈T,F i⊆B) :
    (∑ i∈T,(F i).card)≤B.card := by
  classical
  have q : (T.biUnion F).card = _ := card_biUnion (fun i _ j _ ne => dis ne)
  rw [←q]
  apply card_le_card
  intro z zm
  obtain ⟨i,im,iz⟩ := mem_biUnion.mp zm
  exact incl i im iz

theorem sum_fin_four (p : Fin 4→Nat) : (∑ i,p i)=p 0+p 1+p 2+p 3 := by
  rw [show (univ:Finset (Fin 4))={0,1,2,3} by decide,
      sum_insert (show (0:Fin 4)∉({1,2,3}:Finset (Fin 4)) by decide),
      sum_insert (show (1:Fin 4)∉({2,3}:Finset (Fin 4)) by decide),
      sum_insert (show (2:Fin 4)∉({3}:Finset (Fin 4)) by decide),sum_singleton]
  omega

theorem sum_fin_three (p : Fin 3→Nat) : (∑ i,p i)=p 0+p 1+p 2 := by
  rw [show (univ:Finset (Fin 3))={0,1,2} by decide,
      sum_insert (show (0:Fin 3)∉({1,2}:Finset (Fin 3)) by decide),
      sum_insert (show (1:Fin 3)∉({2}:Finset (Fin 3)) by decide),sum_singleton]
  omega

/-- Four components of a three-cut cannot all supply a high port to
one terminal. Each such port costs four local port-or-distance-two
slots, but the four foreign sums cap the total port count at eight. -/
theorem not_four_high_port_shores (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S : Finset V} (ss : S.card=3) (A : Fin 4→Finset V)
    (sh : ∀ i,Shore G S (A i)) (dis : Pairwise fun i j => Disjoint (A i) (A j))
    {a : V} (as' : a∈S) (hi : ∀ i, ∃ x∈ports G (A i) a,6≤G.degree x) : False := by
  classical
  let p (i : Fin 4) := (ports G (A i) a).card
  let q (i : Fin 4) := (localTwo G (A i) a).card
  let P := ∑ i : Fin 4,p i
  have qcap : (∑ i : Fin 4,q i)≤6 :=
    (sum_cards_le univ (fun i=>localTwo G (A i) a)
       (fun _ _ h => (dis h).mono inter_subset_left inter_subset_left)
       (fun _ _ => inter_subset_right)).trans (distanceTwo_le_of_even 6 a (cap a))
  have charges (i : Fin 4) : 4≤p i+q i := by
    obtain ⟨x,xp,xh⟩ := hi i
    have h := (sh i).port_cost hc ss as' xp
    change G.degree x≤p i+q i+2 at h
    omega
  have bound (i : Fin 4) : P≤6+p i := by
    obtain ⟨x,xp,_⟩ := hi i
    have u := sum_cards_le (univ.erase i) (fun j => ports G (A j) a)
      (fun _ _ h => (dis h).mono (filter_subset _ _) (filter_subset _ _))
      (fun j jm _ wy => (sh i).foreign_distance_two (sh j)
        (dis (mem_erase.mp jm).1.symm) hc xp wy)
    have c := u.trans (distanceTwo_le_of_even 6 x (cap x))
    have s := sum_erase_add univ p (mem_univ i)
    change (∑ j∈univ.erase i,p j)≤6 at c
    change _+p i=P at s
    omega
  have b0 := bound 0; have b1 := bound 1; have b2 := bound 2; have b3 := bound 3
  have pe : P=p 0+p 1+p 2+p 3 := by simp [P,sum_fin_four]
  rw [sum_fin_four] at qcap
  have c0 := charges 0; have c1 := charges 1; have c2 := charges 2; have c3 := charges 3
  omega

/-- Under the degree-six #189 hypotheses, a cut of size three in a
3-connected graph cannot leave four pairwise disjoint nonempty shores.
A shore need not be internally connected, only closed off the cut. -/
theorem no_four_shores (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) (A : Fin 4→Finset V)
    (sh : ∀ i,Shore G S (A i)) (dis : Pairwise fun i j => Disjoint (A i) (A j)) : False := by
  classical
  have some_low (a : V) (am : a∈S) :
      ∃ i, ∀ x∈ports G (A i) a,G.degree x<6 := by
    by_contra! nh
    exact not_four_high_port_shores hc cap ss A sh dis am nh
  obtain ⟨t,tm⟩ := card_pos.mp (show 0<S.card by omega)
  obtain ⟨i,il⟩ := some_low t tm
  obtain ⟨s,sm,ts⟩ := (sh i).hit ss conn tm
  have slow := il s (mem_filter.mpr ⟨sm,ts⟩)
  have alone {z : V} (zlow : G.degree z<6) : z=s := by
    by_contra d
    rcases degree z s d with h|h <;> omega
  have shared (a : V) (am : a∈S) :
      G.Adj a s ∧ ∀ x∈A i,G.Adj a x → x=s := by
    obtain ⟨j,jl⟩ := some_low a am
    obtain ⟨u,uj,au⟩ := (sh j).hit ss conn am
    have eq := alone (jl u (mem_filter.mpr ⟨uj,au⟩))
    subst u
    have ij : i=j := by
      by_contra d
      exact disjoint_left.mp (dis d) sm uj
    subst j
    exact ⟨au,fun x xi ax => alone (jl x (mem_filter.mpr ⟨xi,ax⟩))⟩
  have covers (j : Fin 4) (ji : j≠i) : visible G S (A j)⊆DistanceTwo G s := by
    intro z zm
    obtain ⟨zj,a,am,za⟩ := mem_filter.mp zm
    have vz : s≠z := fun e => disjoint_left.mp (dis ji.symm) sm (e ▸ zj)
    have no : ¬G.Adj s z := fun h => ((sh i).closed s sm z h).elim
      (fun q => disjoint_left.mp (dis ji.symm) q zj)
      (fun q => disjoint_left.mp (sh j).disjoint zj q)
    exact two_of_common hc vz no (shared a am).1.symm za.symm
  have three (j : Fin 4) (ji : j≠i) : 3≤(visible G S (A j)).card := by
    obtain ⟨u,um⟩ := (sh j).nonempty
    have ne : u≠s := fun e=>disjoint_left.mp (dis ji) um (e.symm ▸ sm)
    have high := (degree u s ne).resolve_right (by omega)
    have bd := (sh j).degree_bound um
    exact (sh j).visible_lower ss conn (by omega)
  let T := (univ : Finset (Fin 4)).erase i
  have b := (sum_cards_le T (fun j=>visible G S (A j))
    (fun _ _ h => (dis h).mono (filter_subset _ _) (filter_subset _ _))
    (fun j jm=>covers j (mem_erase.mp jm).1)).trans (distanceTwo_le_of_even 6 s (cap s))
  have c := sum_le_sum (s:=T) (f:=fun _=>3) (g:=fun j=>(visible G S (A j)).card)
    (fun j jm=>three j (mem_erase.mp jm).1)
  have t3 : T.card=3 := by dsimp [T]; rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
  have h : (∑ _∈T,(3:Nat))=9 := by simp [t3]
  change (∑ j∈T,(3:Nat)) ≤ ∑ j∈T,(visible G S (A j)).card at c
  rw [h] at c
  omega

#print axioms not_four_high_port_shores
#print axioms no_four_shores
end Graffiti189LongestPath.ThresholdSix.ThreeCut
