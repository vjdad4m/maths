import DegreePayment180
import RepairCost180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both prime tests follow from this single, uncredited witness.
It additionally requires the marked root even outside the chosen parity. -/
def Protected (G : SimpleGraph V) (r : V) (p : Bool) (A : Finset V) : Prop :=
  let P := parity G r p
  ∃ Z,TwoColor G Z ∧ A∩insert r P⊆Z ∧
    1+A.card+P.card≤weightedLeaves G (eligible A P r)+Z.card

noncomputable def allowance (G : SimpleGraph V) (r : V) (p : Bool) (A : Finset V) : ℕ :=
  let P := parity G r p
  weightedLeaves G (eligible A P r)+Fintype.card V-(1+A.card+P.card)

theorem allowance_eq (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) :
    let P := parity G r p
    1+A.card+P.card+allowance G r p A=weightedLeaves G (eligible A P r)+Fintype.card V := by
  intro P
  have h := weighted_order G hc hn r p.toNat A ai
  change A.card+P.card+1≤Fintype.card V+weightedLeaves G (eligible A P r) at h
  unfold allowance;change 1+A.card+P.card+(weightedLeaves G (eligible A P r)+Fintype.card V-(1+A.card+P.card))=_
  omega

theorem protected_iff (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) :
    Protected G r p A ↔ ∃ Z,TwoColor G Z ∧ A∩insert r (parity G r p)⊆Z ∧
      Fintype.card V-Z.card≤allowance G r p A := by
  have eq := allowance_eq G hc hn r p A ai
  constructor <;> rintro ⟨Z,col,keep,ok⟩ <;> refine ⟨Z,col,keep,?_⟩ <;> have := card_le_univ Z <;> omega

theorem protected_degree (G : SimpleGraph V) (hc : G.Connected) (high : 2<Fintype.card V)
    (r t : V) (p : Bool) (A : Finset V) (ai : Indep G A) (tm : t∈A∩insert r (parity G r p)) :
    G.degree t-2≤allowance G r p A := by
  have eq := allowance_eq G hc (by omega) r p A ai
  obtain ⟨ta,rp⟩ := mem_inter.mp tm
  by_cases pt : t∈parity G r p
  · have := double_degree G hc high r t p A ai ta pt;omega
  · obtain rfl := (mem_insert.mp rp).resolve_right pt
    have single : t∈(A∪parity G t p)\(A∩parity G t p) := by simp [ta,pt]
    have := root_reserve G hc (by omega) t p A ai single;omega

theorem rank_allowance (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+2) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) :
    Fintype.card V-bipartiteNum G≤allowance G r p A := by
  have low := (RootEar.family_of_rank G hc hn rk).rooted r p A ai
  have eq := allowance_eq G hc hn r p A ai
  change 1+A.card+(parity G r p).card≤weightedLeaves G (eligible A (parity G r p) r)+bipartiteNum G at low
  omega

theorem protected_tests (G : SimpleGraph V) (r : V) (good : ∀ p A,Indep G A → Protected G r p A) :
    PrimeTests G r := by
  constructor
  · intro p A ai
    obtain ⟨Z,col,keep,ok⟩ := good p A ai
    exact ⟨Z,col,fun x xm => keep (mem_inter.mpr ⟨(mem_inter.mp xm).1,mem_insert_of_mem (mem_inter.mp xm).2⟩),ok⟩
  · intro I ii ir
    obtain ⟨Z,col,keep,ok⟩ := good true I ii
    refine ⟨Z,col,insert_subset (keep (mem_inter.mpr ⟨ir,mem_insert_self ..⟩)) (fun x xm => ?_),?_⟩
    · exact keep (mem_inter.mpr ⟨(mem_inter.mp xm).1,mem_insert_of_mem (mem_inter.mp xm).2⟩)
    · exact ok.trans (Nat.le_add_right _ _)

theorem protected_bip (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (bi : TwoColor G univ) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) : Protected G r p A := by
  apply (protected_iff G gc hn r p A ai).mpr
  exact ⟨univ,bi,subset_univ _,by simp⟩

#print axioms protected_iff
#print axioms protected_degree
#print axioms rank_allowance
#print axioms protected_tests
end Minimal180.Transversals
