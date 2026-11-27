import SingleLabel
namespace Graffiti189SingletonCage
open GraphPathLift Finset SimpleGraph
open Graffiti189LongestPath.FourCut.Three
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {r a b : V}
variable (S : SingleRoot G r a b)

lemma exclusiveA_eq : exclusiveA S = S.ports.filter (fun v=>¬G.Adj b v) := by
  ext v
  simp only [exclusiveA,mem_filter]
  constructor
  · exact fun h=>⟨h.1,h.2.2⟩
  · intro h
    exact ⟨h.1,(mem_filter.mp h.1).2.resolve_right h.2,h.2⟩

lemma exclusiveB_eq : exclusiveB S = S.ports.filter (fun v=>¬G.Adj a v) := by
  ext v
  simp only [exclusiveB,mem_filter]
  constructor
  · exact fun h=>⟨h.1,h.2.2⟩
  · intro h
    exact ⟨h.1,(mem_filter.mp h.1).2.resolve_left h.2,h.2⟩

def swapped : SingleRoot G r b a :=
  ⟨S.con,S.ab.symm,S.right,S.left,fun v h=>(S.only v h).symm,S.even⟩

lemma swapped_off : (swapped S).off3=S.off3 := by
  ext x; simp [SingleRoot.mem_off3,and_comm]
lemma swapped_ports : (swapped S).ports=S.ports := by
  simp [SingleRoot.ports,swapped_off S,or_comm]
lemma swapped_A : exclusiveA (swapped S)=exclusiveB S := by
  unfold exclusiveA exclusiveB
  rw [swapped_ports S]
lemma swapped_B : exclusiveB (swapped S)=exclusiveA S := by
  unfold exclusiveA exclusiveB
  rw [swapped_ports S]

private lemma split_of_filter (P : Finset V) (q : V→Prop) [DecidablePred q] :
    (P.filter q).card+(P.filter (fun v=>¬q v)).card=P.card := by
  have h : Disjoint (P.filter q) (P.filter (fun v=>¬q v)) := disjoint_left.mpr
    (fun x a b=>(mem_filter.mp b).2 (mem_filter.mp a).2)
  have eq : P.filter q ∪ P.filter (fun v=>¬q v)=P := by
    ext x
    by_cases yes : q x <;> simp [yes]
  rw [←card_union_of_disjoint h,eq]

lemma degree_b_budget (four : S.ports.card=4) (high : 4≤G.degree b) :
    (exclusiveA S).card≤1+(if G.Adj a b then 1 else 0) := by
  let P := S.ports.filter (G.Adj b)
  let E := ({a}:Finset V).filter (fun _=>G.Adj a b)
  have partition := split_of_filter S.ports (G.Adj b)
  rw [←exclusiveA_eq S,four] at partition
  have sub : G.neighborFinset b ⊆ insert r (E ∪ P) := by
    intro v hv
    have bv := (G.mem_neighborFinset _ _).mp hv
    by_cases er : v=r
    · simp [er]
    by_cases ea : v=a
    · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inl
        (mem_filter.mpr ⟨mem_singleton.mpr ea,ea ▸ bv.symm⟩))))
    have eb : v≠b := bv.ne.symm
    have off := S.mem_off3.mpr ⟨er,ea,eb⟩
    exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr
      (mem_filter.mpr ⟨mem_filter.mpr ⟨off,Or.inr bv⟩,bv⟩))))
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have h₁ := card_insert_le r (E ∪ P)
  have h₂ := card_union_le E P
  have e : E.card=(if G.Adj a b then 1 else 0) := by
    by_cases e : G.Adj a b <;> simp [E,e]
  change P.card+ (exclusiveA S).card=4 at partition
  rw [e] at h₂
  omega

lemma degree_a_budget (four : S.ports.card=4) (high : 4≤G.degree a) :
    (exclusiveB S).card≤1+(if G.Adj a b then 1 else 0) := by
  have h := degree_b_budget (swapped S) (by rw [swapped_ports S,four]) high
  rw [swapped_A S] at h
  by_cases e : G.Adj a b
  · have e' : G.Adj b a := e.symm
    simpa only [e, e', if_true] using h
  · have e' : ¬G.Adj b a := fun g => e g.symm
    simpa only [e, e', if_false] using h

lemma classes_cap (four : S.ports.card=4) (ha : 4≤G.degree a) (hb : 4≤G.degree b) :
   let x := (exclusiveA S).card
   let y := (exclusiveB S).card
   let edge := G.Adj a b
   7≤Fintype.card V ∧ Fintype.card V≤13 ∧
    x≤1+(if edge then 1 else 0) ∧ y≤1+(if edge then 1 else 0) ∧
    (x=0 ∨ y=0 → Fintype.card V≤11) ∧
    (edge → Fintype.card V+x+y≤15) := by
  dsimp
  have t := S.total_card four
  refine ⟨by omega,S.order_le_thirteen four,degree_b_budget S four hb,degree_a_budget S four ha,?_,?_⟩
  · intro e
    apply S.order_le_eleven_of_common four
    rcases e with h|h
    · right; intro v vp
      by_contra no
      have m : v∈exclusiveA S := by
        rw [exclusiveA_eq S]; exact mem_filter.mpr ⟨vp,no⟩
      exact (Nat.not_lt_zero _ (h ▸ card_pos.mpr ⟨v,m⟩))
    · left; intro v vp
      by_contra no
      have m : v∈exclusiveB S := by
        rw [exclusiveB_eq S]; exact mem_filter.mpr ⟨vp,no⟩
      exact (Nat.not_lt_zero _ (h ▸ card_pos.mpr ⟨v,m⟩))
  · intro e
    have n := S.order_plus_exclusive_le_fifteen four e
    rw [SingleRoot.exclusiveTags, card_disjSum,←exclusiveA_eq S,←exclusiveB_eq S] at n
    omega
#print axioms classes_cap
end Graffiti189SingletonCage
