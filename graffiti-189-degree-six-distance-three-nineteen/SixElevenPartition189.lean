import SixElevenCharges189
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def sixClass (G : SimpleGraph V) [DecidableRel G.Adj] (a b x : V) : Fin 8 :=
  if G.Adj a x then if G.dist b x=2 then 1 else 0
  else if G.Adj b x then if G.dist a x=2 then 3 else 2
  else if G.dist a x=2 then if G.dist b x=2 then 6 else 4
  else if G.dist b x=2 then 5 else 7

def sixClassSpec (G : SimpleGraph V) (a b x : V) (k : Fin 8) : Prop :=
  match k.val with
  | 0 => G.Adj a x ∧ G.dist b x≠2
  | 1 => G.Adj a x ∧ G.dist b x=2
  | 2 => G.Adj b x ∧ G.dist a x≠2
  | 3 => G.Adj b x ∧ G.dist a x=2
  | 4 => ¬G.Adj a x ∧ ¬G.Adj b x ∧ G.dist a x=2 ∧ G.dist b x≠2
  | 5 => ¬G.Adj a x ∧ ¬G.Adj b x ∧ G.dist a x≠2 ∧ G.dist b x=2
  | 6 => ¬G.Adj a x ∧ ¬G.Adj b x ∧ G.dist a x=2 ∧ G.dist b x=2
  | _ => ¬G.Adj a x ∧ ¬G.Adj b x ∧ G.dist a x≠2 ∧ G.dist b x≠2

theorem class_spec {a b x : V} (no : ¬(G.Adj a x ∧ G.Adj b x)) (k : Fin 8) :
    sixClass G a b x=k ↔ sixClassSpec G a b x k := by
  fin_cases k <;>
    by_cases ax : G.Adj a x <;> by_cases bx : G.Adj b x <;>
    by_cases da : G.dist a x=2 <;> by_cases db : G.dist b x=2
  all_goals first | exact (no ⟨ax,bx⟩).elim | simp [sixClass,sixClassSpec,ax,bx,da,db]

noncomputable def sixBucket (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V)
    (S : Finset V) (k : Fin 8) : Finset V := S.filter (fun x=>sixClass G a b x=k)

theorem mem_sixBucket {a b x : V} {S : Finset V} (h : ¬(G.Adj a x ∧ G.Adj b x)) (k : Fin 8) :
    x∈sixBucket G a b S k ↔ x∈S ∧ sixClassSpec G a b x k := by
  simp only [sixBucket,mem_filter,class_spec h]

theorem sixBuckets_card (a b : V) (S : Finset V) :
    (sixBucket G a b S 0).card+(sixBucket G a b S 1).card+
    (sixBucket G a b S 2).card+(sixBucket G a b S 3).card+
    (sixBucket G a b S 4).card+(sixBucket G a b S 5).card+
    (sixBucket G a b S 6).card+(sixBucket G a b S 7).card=S.card := by
  have h : S.card=∑ k : Fin 8,(sixBucket G a b S k).card :=
    card_eq_sum_card_fiberwise (f:=sixClass G a b) (s:=S) (t:=univ) (by intro x hx; simp)
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero] at h
  change S.card = (sixBucket G a b S 0).card+((sixBucket G a b S 1).card+
    ((sixBucket G a b S 2).card+((sixBucket G a b S 3).card+
    ((sixBucket G a b S 4).card+((sixBucket G a b S 5).card+
    ((sixBucket G a b S 6).card+(sixBucket G a b S 7).card)))))) at h
  omega

theorem sixBuckets_disjoint (a b : V) (S T : Finset V) {i j : Fin 8} (ij : i≠j) :
    Disjoint (sixBucket G a b S i) (sixBucket G a b T j) := by
  refine disjoint_left.mpr (fun x xi xj=>ij ?_)
  exact (mem_filter.mp xi).2.symm.trans (mem_filter.mp xj).2

theorem sixBucket_lt_has_high (a b : V) (S : Finset V) (k : Fin 8) :
    (sixBucket G a b (S.filter (fun v=>G.degree v<6)) k).card <
      (sixBucket G a b S k).card → ∃ x∈sixBucket G a b S k,6≤G.degree x := by
  intro lt
  by_contra h
  have sub : sixBucket G a b S k⊆sixBucket G a b (S.filter (fun v=>G.degree v<6)) k := by
    intro x hx
    obtain ⟨xs,cl⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨xs,Nat.lt_of_not_ge (fun high=>h ⟨x,hx,high⟩)⟩,cl⟩
  exact (Nat.not_le_of_lt lt) (card_le_card sub)

theorem sixBucket_filter_split (a b : V) (S : Finset V) (k : Fin 8) :
    (sixBucket G a b (S.filter (fun v=>6≤G.degree v)) k).card+
      (sixBucket G a b (S.filter (fun v=>G.degree v<6)) k).card=(sixBucket G a b S k).card := by
  classical
  let H := sixBucket G a b (S.filter (fun v=>6≤G.degree v)) k
  let L := sixBucket G a b (S.filter (fun v=>G.degree v<6)) k
  have e : H∪L=sixBucket G a b S k := by
    ext x
    simp only [H,L,sixBucket,mem_union,mem_filter]
    by_cases h : 6≤G.degree x
    · simp [h,Nat.not_lt_of_ge h]
    · simp [h,Nat.lt_of_not_ge h]
  have d : Disjoint H L := disjoint_left.mpr (fun x xh xl=>
    Nat.not_lt_of_ge (mem_filter.mp (mem_filter.mp xh).1).2 (mem_filter.mp (mem_filter.mp xl).1).2)
  rw [←e,card_union_of_disjoint d]

#print axioms sixBuckets_card
#print axioms class_spec
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
