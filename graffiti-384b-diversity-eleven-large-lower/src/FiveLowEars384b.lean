import HighPrivateEar384b
import DiversityElevenEarDeficit384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem incidence (A B : Finset V) :
    (∑ x ∈ A, nbr G x B) = ∑ y ∈ B, nbr G y A := by
  have eq (x : V) (S : Finset V) : nbr G x S = ∑ y ∈ S, if G.Adj x y then 1 else 0 := by
    simp only [sum_boole,Nat.cast_id,nbr]
  simp only [eq]
  rw [sum_comm]
  exact sum_congr rfl (fun y _ => sum_congr rfl
    (fun x _ => by
      by_cases h : G.Adj x y
      · simp [h,h.symm]
      · have hn : ¬G.Adj y x := fun a => h a.symm
        simp [h,hn]))

/-- Five independent degree-two omissions, at least three of them ordinary
  ears with high endpoints, are enough for the exact diversity-eleven bound. -/
theorem exact_of_five_with_three_ordinary
    (t : (types G).card=11) (nine : (high G).card=9)
    {O : Finset V} (five : O.card=5) (lo : Disjoint O (high G))
    (deg : ∀ e∈O,G.degree e=2)
    (ind : ∀ x∈O,∀ y∈O,¬G.Adj x y)
    {Ord : Finset V} (ord : Ord ⊆ O) (ord3 : 3≤Ord.card)
    (anchors : ∀ e∈Ord,∀ y,G.Adj e y → y∈high G) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  let P := (high G).filter (fun z=>∃ e∈O, G.Adj e z)
  have ps : 9≤P.card := by
    have f := deficit_one_of_independent_low G t nine bad lo
      (fun e em => (deg e em).ge) ind
      (P:=P) (fun z zm ez => mem_filter.mpr ⟨zm,ez⟩)
    omega
  have all {e : V} (em : e∈O) {S : Finset V}
      (sub : G.neighborFinset e ⊆ S) : nbr G e S = 2 := by
    have h : S.filter (G.Adj e)=G.neighborFinset e := by
      ext y
      simp only [mem_filter,mem_neighborFinset]
      exact ⟨And.right,fun ey => ⟨sub ((G.mem_neighborFinset ..).mpr ey),ey⟩⟩
    rw [nbr,h,card_neighborFinset_eq_degree,deg e em]
  have dom : TwoDominates G Oᶜ := by
    intro e eh
    have em : e∈O := by simpa using eh
    rw [all em (S:=Oᶜ) (fun y ym=>mem_compl.mpr (fun yo=>
      ind e em y yo ((G.mem_neighborFinset ..).mp ym)))]
  have sf : (∑ z ∈ P, nbr G z O)≤10 := by
    rw [incidence]
    calc
      (∑ e ∈ O,nbr G e P)≤∑ _ ∈ O,2 := sum_le_sum (fun e em => by
        have inc : P.filter (G.Adj e)⊆G.neighborFinset e := by
          intro x xm
          exact (G.mem_neighborFinset ..).mpr (mem_filter.mp xm).2
        have c := card_le_card inc
        rwa [card_neighborFinset_eq_degree,deg e em] at c)
      _=10 := by simp [five]
  have pos (z : V) (zm : z∈P) : 1≤nbr G z O := by
    obtain ⟨e,em,ez⟩ := (mem_filter.mp zm).2
    exact card_pos.mpr ⟨e,mem_filter.mpr ⟨em,ez.symm⟩⟩
  let k := fun z => nbr G z O-1
  have slack : (∑ z ∈ P,k z)≤1 := by
    have ee : (∑ z ∈ P,nbr G z O)=P.card+∑ z ∈ P,k z := by
      calc
        _ = ∑ z ∈ P,(1+k z) := sum_congr rfl (fun z zm => by
          have h := pos z zm
          dsimp [k]; omega)
        _ = _ := by simp [sum_add_distrib]
    omega
  have single (z : V) (zp : z∈P) : k z≤1 :=
    (single_le_sum (fun y (_:y∈P) => Nat.zero_le (k y)) zp).trans slack
  have unique {z y : V} (zp : z∈P) (yp : y∈P) (zz : 2≤nbr G z O)
      (yy : 2≤nbr G y O) : z=y := by
    by_contra ne
    have pair : ({z,y} : Finset V)⊆P := insert_subset zp (singleton_subset_iff.mpr yp)
    have b := sum_le_sum_of_subset_of_nonneg pair (f:=k)
      (fun i _ _=>Nat.zero_le (k i))
    rw [sum_pair ne] at b
    dsimp [k] at b slack
    omega
  have privateEar : ∃e∈Ord,∀ z,G.Adj e z → nbr G z O≤1 := by
    by_cases rep : ∃ z∈P,2≤nbr G z O
    · obtain ⟨z,zp,zz⟩ := rep
      have cap := single z zp
      obtain ⟨e,em,ez⟩ : ∃ e∈Ord,¬G.Adj z e := by
        by_contra! h
        have sub : Ord ⊆ O.filter (G.Adj z) := fun e em =>
          mem_filter.mpr ⟨ord em,h e em⟩
        have c := card_le_card sub
        unfold k nbr at cap
        omega
      refine ⟨e,em,?_⟩
      intro y ey
      by_contra! yy
      have yp : y∈P := mem_filter.mpr ⟨anchors e em y ey,e,ord em,ey⟩
      exact ez ((unique zp yp zz yy) ▸ ey.symm)
    · obtain ⟨e,em⟩ := card_pos.mp (show 0<Ord.card by omega)
      refine ⟨e,em,?_⟩
      intro y ey
      by_contra! yy
      exact rep ⟨y,mem_filter.mpr ⟨anchors e em y ey,e,ord em,ey⟩,yy⟩
  obtain ⟨e,em,pr⟩ := privateEar
  obtain ⟨a,b,ab,N⟩ := card_eq_two.mp (by rw [card_neighborFinset_eq_degree,deg e (ord em)] :
      (G.neighborFinset e).card=2)
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (N ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp
    (N ▸ mem_insert_of_mem (mem_singleton_self _))
  have ah := anchors e em a ea
  have bh := anchors e em b eb
  have lowa : a∉O := fun am => Finset.disjoint_left.mp lo am ah
  have lowb : b∉O := fun bm => Finset.disjoint_left.mp lo bm bh
  apply (not_le_of_gt bad) (exact_of_five_with_private_ear G t five.ge dom (ord em) lowa lowb ab
    ea.symm eb.symm (mem_filter.mp ah).2 (mem_filter.mp bh).2 ?_)
  intro z zm ze
  have only {u : V} (eu : G.Adj e u) : ¬G.Adj z u := by
    intro zu
    have p : ({z,e} : Finset V) ⊆ O.filter (G.Adj u) := insert_subset
      (mem_filter.mpr ⟨zm,zu.symm⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨ord em,eu.symm⟩))
    have c := card_le_card p
    rw [card_pair ze] at c
    exact (by have h := pr u eu; unfold nbr at h; omega)
  exact ⟨only ea,only eb⟩

#print axioms exact_of_five_with_three_ordinary
end Graffiti384b.DiversityEleven
