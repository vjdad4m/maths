import Partial133
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

namespace Graffiti133FourPortPacking
open SimpleGraph Finset Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def portMask (G : SimpleGraph V) (P : Finset V) (x : V) : Finset V :=
  P.filter (G.Adj x)

noncomputable def portExcess (G : SimpleGraph V) (P Q : Finset V) : ℕ :=
  ∑ x ∈ Q, ((portMask G P x).card-1)

noncomputable def representedPortPairs (G : SimpleGraph V) (P M : Finset V) : Finset (Finset V) :=
  M.biUnion (fun x => (portMask G P x).powersetCard 2)

@[simp] theorem mem_portMask (P : Finset V) (x p : V) :
    p∈portMask G P x ↔ p∈P ∧ G.Adj x p := by simp [portMask]

theorem mem_representedPortPairs (P M : Finset V) (s : Finset V) :
    s∈representedPortPairs G P M ↔ s.card=2 ∧
      ∃ x∈M, ∀ v∈s,v∈P ∧ G.Adj x v := by
  simp only [representedPortPairs,Finset.mem_biUnion,Finset.mem_powersetCard,
    Finset.subset_iff,mem_portMask]
  tauto

theorem port_masks_inter_le_one (h4 : FourCycleFree G) (P : Finset V) {x y : V} (ne : x≠y) :
    (portMask G P x ∩ portMask G P y).card≤1 := by
  by_contra! h
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp h
  have spec (p : V) (m : p∈portMask G P x ∩ portMask G P y) : G.Adj x p ∧ G.Adj y p :=
    ⟨(mem_portMask P x p |>.mp (Finset.mem_inter.mp m).1).2,
      (mem_portMask P y p |>.mp (Finset.mem_inter.mp m).2).2⟩
  exact ab (h4 x y a b ne (spec a ha).1 (spec a ha).2 (spec b hb).1 (spec b hb).2)

theorem multivalent_mask_injective (h4 : FourCycleFree G) (P : Finset V) {x y : V}
    (multi : 2 ≤ (portMask G P x).card) (eq : portMask G P x=portMask G P y) : x=y := by
  by_contra ne
  have h := port_masks_inter_le_one h4 P ne
  rw [←eq,Finset.inter_self] at h
  omega

theorem represented_card (h4 : FourCycleFree G) (P S : Finset V) :
    (representedPortPairs G P S).card=∑ x∈S, (portMask G P x).card.choose 2 := by
  classical
  unfold representedPortPairs
  have dis : (S : Set V).PairwiseDisjoint (fun x => (portMask G P x).powersetCard 2) := by
    intro x _ y _ ne
    apply Finset.disjoint_left.mpr
    intro T tx ty
    obtain ⟨subx,n⟩ := Finset.mem_powersetCard.mp tx
    obtain ⟨suby,_⟩ := Finset.mem_powersetCard.mp ty
    have sub : T⊆portMask G P x ∩ portMask G P y :=
      fun a am => Finset.mem_inter.mpr ⟨subx am,suby am⟩
    have c := (Finset.card_le_card sub).trans (port_masks_inter_le_one h4 P ne)
    omega
  rw [Finset.card_biUnion dis]
  simp only [Finset.card_powersetCard]

private theorem represented_subset (P S : Finset V) :
    representedPortPairs G P S ⊆ P.powersetCard 2 := by
  intro A h
  obtain ⟨Count,x,xS,info⟩ := (mem_representedPortPairs P S A).mp h
  exact Finset.mem_powersetCard.mpr ⟨fun v vm=>(info v vm).1,Count⟩

/-- Each port pair can have at most one witness, regardless of whether the
witness is inside or outside the core. -/
theorem pair_charge (h4 : FourCycleFree G) (P Q M : Finset V) (dis : Disjoint Q M) :
    (∑ x ∈ Q, (portMask G P x).card.choose 2)+(representedPortPairs G P M).card
      ≤ P.card.choose 2 := by
  classical
  have bound := Finset.card_le_card (represented_subset (G:=G) P (Q∪M))
  rw [represented_card h4,Finset.card_powersetCard,Finset.sum_union dis] at bound
  rwa [represented_card h4]

private theorem excess_le_choose_two (n : ℕ) : n-1≤n.choose 2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    omega

theorem portExcess_le_pair_weight (P Q : Finset V) :
    portExcess G P Q≤∑ x∈Q, (portMask G P x).card.choose 2 := by
  exact Finset.sum_le_sum fun _ _=>excess_le_choose_two _

theorem crossings_le_nonports_add_pairs (h4 : FourCycleFree G) (P M : Finset V) :
    (∑ x∈M,(portMask G P x).card)≤M.card+(representedPortPairs G P M).card := by
  rw [represented_card h4]
  calc
    _ ≤ ∑ x∈M, (1+(portMask G P x).card.choose 2) :=
      Finset.sum_le_sum fun x _=> by have h:=excess_le_choose_two (portMask G P x).card; omega
    _ = _ := by simp [Finset.sum_add_distrib]

theorem port_rows_commute (P M : Finset V) :
    (∑ p∈P, (portMask G M p).card)=(∑ x∈M,(portMask G P x).card) := by
  classical
  simp only [portMask,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro p _
  exact if_congr (G.adj_comm _ _) rfl rfl

/-- With four ports and outside excess at least five, at most one port pair
has a shared neighbor from any disjoint family of inner core nonports. -/
theorem inner_pairs_at_most_one (h4 : FourCycleFree G) (P Q M : Finset V)
    (four : P.card=4) (dis : Disjoint Q M) (high : 5≤portExcess G P Q) :
    (representedPortPairs G P M).card≤1 := by
  have bound := pair_charge h4 P Q M dis
  have weight := portExcess_le_pair_weight (G:=G) P Q
  rw [four,show Nat.choose 4 2=6 by decide] at bound
  omega

theorem inner_crossings_at_most_order_add_one (h4 : FourCycleFree G) (P Q M : Finset V)
    (four : P.card=4) (dis : Disjoint Q M) (high : 5≤portExcess G P Q) :
    (∑ p∈P,(portMask G M p).card)≤M.card+1 := by
  rw [port_rows_commute]
  have a := crossings_le_nonports_add_pairs h4 P M
  have b := inner_pairs_at_most_one h4 P Q M four dis high
  omega

private theorem mask_sub (P : Finset V) (x : V) : portMask G P x⊆P :=
  fun a h=>(mem_portMask P x a |>.mp h).1

/-- If one outside vertex meets all four ports, the entire outside excess
is precisely three. -/
theorem full_mask_forces_excess_three (h4 : FourCycleFree G) (P Q : Finset V)
    (four : P.card=4) {x : V} (xm : x∈Q) (full : (portMask G P x).card=4) :
    portExcess G P Q=3 := by
  have eq : portMask G P x=P :=
    Finset.eq_of_subset_of_card_le (mask_sub P x) (by omega)
  have each (y : V) (ne : y≠x) : (portMask G P y).card≤1 := by
    have h:=port_masks_inter_le_one h4 P ne
    rw [eq,Finset.inter_eq_left.mpr (mask_sub P y)] at h
    exact h
  unfold portExcess
  rw [Finset.sum_eq_single_of_mem x xm]
  · omega
  · intro y _ ne
    have h := each y ne
    omega

private theorem triple_mask_unique (h4 : FourCycleFree G) (P : Finset V) (four : P.card=4)
    {x y : V} (x3 : (portMask G P x).card=3) (y3 : (portMask G P y).card=3) : x=y := by
  by_contra ne
  have inter := port_masks_inter_le_one h4 P ne
  have uni := Finset.card_le_card (Finset.union_subset (mask_sub (G:=G) P x) (mask_sub (G:=G) P y))
  have id := Finset.card_union_add_card_inter (s:=portMask G P x) (t:=portMask G P y)
  omega

/-- Four-port high-excess classification. A size-four mask cannot appear.
If a size-three mask appears, it is unique, and there are at most three
size-two witnesses. Distinct multivalent masks always differ by
`multivalent_mask_injective`. -/
theorem high_excess_profiles (h4 : FourCycleFree G) (P Q : Finset V)
    (four : P.card=4) (high : 4≤portExcess G P Q) :
    (∀ x∈Q,(portMask G P x).card≤1 ∨ (portMask G P x).card=2) ∨
    ∃ x∈Q,(portMask G P x).card=3 ∧
      (∀ y∈Q,y≠x→(portMask G P y).card≤1 ∨ (portMask G P y).card=2) ∧
      (Q.filter fun y => (portMask G P y).card=2).card≤3 := by
  classical
  have cap (x : V) (xm : x∈Q) : (portMask G P x).card≤3 := by
    have h := Finset.card_le_card (mask_sub (G:=G) P x)
    have ne : (portMask G P x).card≠4 := fun f=>by
      have e:=full_mask_forces_excess_three h4 P Q four xm f
      omega
    omega
  by_cases has : ∃ x∈Q,(portMask G P x).card=3
  · obtain ⟨x,xm,x3⟩ := has
    apply Or.inr
    have others (y : V) (ym : y∈Q) (ne : y≠x) : (portMask G P y).card≤1 ∨ (portMask G P y).card=2 := by
      have e := cap y ym
      have n : (portMask G P y).card≠3 := fun h => ne (triple_mask_unique h4 P four h x3)
      omega
    refine ⟨x,xm,x3,others,?_⟩
    let A := Q.filter fun y => (portMask G P y).card=2
    have xa : x∉A := by simp [A,x3]
    have sub : insert x A⊆Q := Finset.insert_subset_iff.mpr ⟨xm,Finset.filter_subset _ _⟩
    have over := pair_charge h4 P Q ∅ (by simp)
    have total : (∑ y∈Q,(portMask G P y).card.choose 2)≤6 := by
      simpa [four,representedPortPairs] using over
    have b : (∑ y∈insert x A,(portMask G P y).card.choose 2) ≤
        ∑ y∈Q,(portMask G P y).card.choose 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (by simp)
    have ca : (∑ y∈A,(portMask G P y).card.choose 2)=A.card := by
      calc
        _ = ∑ _y∈A,(1:ℕ) := Finset.sum_congr rfl fun y ym=>by
          rw [(Finset.mem_filter.mp ym).2]
          decide
        _ = _ := by simp
    rw [Finset.sum_insert xa,x3,ca,show Nat.choose 3 2=3 by decide] at b
    change A.card≤3
    omega
  · apply Or.inl
    intro x xm
    have a := cap x xm
    have ne : (portMask G P x).card≠3 := fun h=>has ⟨x,xm,h⟩
    omega

/-- Excess equals the size-two count plus twice the size-three count
when there are no larger masks. -/
theorem portExcess_counts (P Q : Finset V)
    (cap : ∀ x∈Q,(portMask G P x).card≤3) :
    portExcess G P Q =
      (Q.filter fun x => (portMask G P x).card=2).card+
        2*(Q.filter fun x => (portMask G P x).card=3).card := by
  classical
  unfold portExcess
  calc
    _ = ∑ x∈Q, ((if (portMask G P x).card=2 then 1 else 0) +
        (if (portMask G P x).card=3 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro x xm
      have c := cap x xm
      split <;> split <;> omega
    _ = _ := by
      rw [Finset.sum_add_distrib,←Finset.sum_filter,←Finset.sum_filter]
      simp [Nat.mul_comm]

/-- For excess at least five, the exact two possibilities are five or
six size-two masks, or one size-three and three size-two masks. -/
theorem high_five_profile_counts (h4 : FourCycleFree G) (P Q : Finset V)
    (four : P.card=4) (high : 5≤portExcess G P Q) :
    let A := Q.filter fun x => (portMask G P x).card=2
    let T := Q.filter fun x => (portMask G P x).card=3
    (T.card=0 ∧ 5≤A.card ∧ A.card≤6) ∨ (T.card=1 ∧ A.card=3) := by
  classical
  let A := Q.filter fun x => (portMask G P x).card=2
  let T := Q.filter fun x => (portMask G P x).card=3
  change (T.card=0 ∧ 5≤A.card ∧ A.card≤6) ∨ (T.card=1 ∧ A.card=3)
  have capE := (portExcess_le_pair_weight (G:=G) P Q).trans ((pair_charge h4 P Q ∅ (by simp)).trans'
    (by simp [representedPortPairs]))
  have bound : portExcess G P Q≤6 := by simpa [four] using capE
  rcases high_excess_profiles h4 P Q four (by omega) with no | ⟨x,xm,x3,others,capA⟩
  · have empty : T=∅ := by
      ext y
      constructor
      · intro h
        obtain ⟨a,b⟩ := Finset.mem_filter.mp h
        rcases no y a with c | c <;> omega
      · intro h
        simp at h
    have e : portExcess G P Q=A.card+2*T.card :=
      portExcess_counts P Q fun y ym=> by rcases no y ym with c | c <;> omega
    have z : T.card=0 := by simp [empty]
    exact Or.inl ⟨z,by omega,by omega⟩
  · have onlyX : T={x} := by
      ext y
      simp only [T,Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨ym,hy⟩
        exact triple_mask_unique h4 P four hy x3
      · rintro rfl
        exact ⟨xm,x3⟩
    have t1 : T.card=1 := by simp [onlyX]
    have e : portExcess G P Q=A.card+2*T.card := portExcess_counts P Q fun y ym=>by
      by_cases h : y=x
      · simp [h,x3]
      · rcases others y ym h with c | c <;> omega
    change A.card≤3 at capA
    exact Or.inr ⟨t1,by omega⟩

/-- Count triple masks with their extra unit of pair consumption. -/
theorem charge_with_triples (h4 : FourCycleFree G) (P Q M : Finset V) (dis : Disjoint Q M) :
    portExcess G P Q+(Q.filter fun x => (portMask G P x).card=3).card+
      (representedPortPairs G P M).card ≤ P.card.choose 2 := by
  classical
  have weight : portExcess G P Q+(Q.filter fun x => (portMask G P x).card=3).card
      ≤ ∑ x∈Q,(portMask G P x).card.choose 2 := by
    unfold portExcess
    rw [Finset.card_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases h : (portMask G P x).card=3
    · simp [h]
    · simpa [h] using excess_le_choose_two (portMask G P x).card
  exact (Nat.add_le_add_right weight _).trans (pair_charge h4 P Q M dis)

theorem high_five_with_inner_pair_is_five_two_masks (h4 : FourCycleFree G) (P Q M : Finset V)
    (four : P.card=4) (dis : Disjoint Q M) (high : 5≤portExcess G P Q)
    (positive : 1≤(representedPortPairs G P M).card) :
    portExcess G P Q=5 ∧ (representedPortPairs G P M).card=1 ∧
      (Q.filter fun x => (portMask G P x).card=3).card=0 ∧
      (Q.filter fun x => (portMask G P x).card=2).card=5 := by
  have b := charge_with_triples h4 P Q M dis
  rw [four,show Nat.choose 4 2=6 by decide] at b
  have noFour (x : V) (xm : x∈Q) : (portMask G P x).card≤3 := by
    have h := Finset.card_le_card (mask_sub (G:=G) P x)
    have ne : (portMask G P x).card≠4 := fun f=>by
      have e:=full_mask_forces_excess_three h4 P Q four xm f
      omega
    omega
  have eq := portExcess_counts P Q noFour
  omega

#print axioms pair_charge
#print axioms inner_pairs_at_most_one
#print axioms crossings_le_nonports_add_pairs
#print axioms inner_crossings_at_most_order_add_one
#print axioms high_excess_profiles
#print axioms high_five_profile_counts
#print axioms charge_with_triples
#print axioms high_five_with_inner_pair_is_five_two_masks
end Graffiti133FourPortPacking
