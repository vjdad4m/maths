import DeletedRoot180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected dominating set and a payment for its marked vertices. -/
theorem core_payment (G : SimpleGraph V) (r : V) (A P D : Finset V)
    (hc : Con G D) (dom : ∀ v∉D,Dominates G D v)
    (root : r∈D ∨ r∈A∩P ∨ r∉A∪P)
    (pay : 1+(A∩P).card+((A∪P)∩D).card≤bipartiteNum G) :
    1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  classical
  have lf := weightedCore G D (eligible A P r) hc dom
  have eq : eligible A P r\D=(A∪P)\D := by
    ext v
    simp only [eligible_iff,mem_sdiff,mem_union]
    by_cases h : v=r
    · subst v; simp only [mem_inter,mem_union] at root; tauto
    · tauto
  rw [eq] at lf
  have u := card_union_add_card_inter A P
  have s := card_sdiff_add_card_inter (A∪P) D
  omega

omit [Fintype V] in
theorem pair_indep (G : SimpleGraph V) {x y : V} (no : ¬G.Adj x y) : Indep G {x,y} := by
  intro a ha b hb ne e
  simp only [mem_insert,mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | exact ne rfl | exact no e | exact no e.symm

theorem pair_credit (G : SimpleGraph V) {A : Finset V} (ind : Indep G A) {u v : V}
    (uv : u≠v) (no : ¬G.Adj u v) (ou : u∉A) (ov : v∉A) : A.card+2≤bipartiteNum G := by
  classical
  simpa [card_pair uv] using bip_bound G ind (pair_indep G no)
    (show Disjoint A {u,v} by simp [disjoint_insert_right,ou,ov])

theorem one_credit (G : SimpleGraph V) {A : Finset V} (ind : Indep G A) {u : V}
    (ou : u∉A) : A.card+1≤bipartiteNum G := by
  classical
  simpa using bip_bound G ind (show Indep G {u} by simp [Indep]) (disjoint_singleton_right.mpr ou)

def Universal (G : SimpleGraph V) (r : V) : Prop := ∀ x,x≠r → G.Adj x r

theorem universal_pay (G : SimpleGraph V) {r c : V} (u : Universal G c) (A P : Finset V)
    (root : r=c ∨ r∈A∩P ∨ r∉A∪P)
    (pay : 1+(A∩P).card+(if c∈A∪P then 1 else 0)≤bipartiteNum G) :
    1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  classical
  apply core_payment G r A P {c} (con_single ..) (fun v hv => ⟨c,mem_singleton_self _,u v (by simpa using hv)⟩)
    (by simpa using root)
  by_cases h : c∈A∪P <;> simpa [inter_singleton_of_mem,inter_singleton_of_not_mem,h] using pay

theorem rank_small_complete (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (small : bipartiteNum G<3) : ∀ r,Universal G r := by
  classical
  intro r x ne
  by_contra no
  obtain ⟨y,xy⟩ := exists_adj G gc hn x
  have yr : y≠r := fun h => no (h ▸ xy)
  have b := pair_credit G (show Indep G {y} by simp [Indep]) ne no
    (by simpa using xy.ne) (by simpa using yr.symm)
  rw [card_singleton] at b
  omega

#print axioms core_payment
#print axioms pair_credit
#print axioms one_credit
#print axioms universal_pay
#print axioms rank_small_complete
end Minimal180.Substitution
