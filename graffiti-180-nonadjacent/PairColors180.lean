import ConflictRepair180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def sideNeighbors (G : SimpleGraph V) (v : V) (c : V→Bool) (s : Bool) :=
  (G.neighborFinset v).filter (fun x => c x=s)

omit [DecidableEq V] in
theorem sides_sum (G : SimpleGraph V) (v : V) (c : V→Bool) :
    (sideNeighbors G v c false).card+(sideNeighbors G v c true).card=G.degree v := by
  classical
  have h := filter_card_add_filter_neg_card_eq_card (s:=G.neighborFinset v) (p:=fun x => c x=false)
  have eq : (G.neighborFinset v).filter (fun x => ¬c x=false)=sideNeighbors G v c true := by
    ext x;simp [sideNeighbors]
  rw [eq,card_neighborFinset_eq_degree] at h;exact h

/-- At a failed single-protected marking the budget is exactly two and
every coloring of the bipartite remainder splits the four neighbors 2:2. -/
theorem solo_rigidity (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (a b : V) (ne : a≠b) (bi : TwoColor G (univ\{a,b}))
    (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p)) :
    G.degree a=4 ∧ allowance G r p A=2 ∧ ∀ c : V→Bool,ProperOn G (univ\{a,b}) c →
        ∀ s,(sideNeighbors G a c s).card=2 := by
  classical
  let K := A∩insert r (parity G r p)
  let X : Finset V := {a,b}
  have four : G.degree a=4 := by
    rcases (pair_obstruction G gc hn r p A ai bad a b ne bi).2 with h|h|h
    · exact h.2.2
    · exact (h.2.1 ak).elim
    · exact (bk h.2.1).elim
  have isect : X∩K={a} := by
    ext x
    constructor
    · intro xm
      have alt := mem_insert.mp (mem_inter.mp xm).1
      rcases alt with eq|mem
      · exact mem_singleton.mpr eq
      · exact (bk (mem_singleton.mp mem ▸ (mem_inter.mp xm).2)).elim
    · intro xm
      obtain rfl := mem_singleton.mp xm
      exact mem_inter.mpr ⟨mem_insert_self ..,ak⟩
  have lower := (budget_two G gc hn r p A ai bad a b ne bi).1
  have bound (c : V→Bool) (cp : ProperOn G (univ\X) c) (s : Bool) :
      allowance G r p A<1+(sideNeighbors G a c s).card := by
    have cost := conflict_failure G gc hn r p A X ai bad c (fun _ => s) cp
    change allowance G r p A<(X\K).card+(conflicts G (univ\X) (X∩K) c (fun _ => s)).card at cost
    rw [pair_free a b K ak bk,card_singleton,isect] at cost
    have sub : conflicts G (univ\X) {a} c (fun _ => s)⊆sideNeighbors G a c s := by
      intro y ym
      obtain ⟨t,tm,ed,eq⟩ := (mem_filter.mp ym).2
      obtain rfl := mem_singleton.mp tm
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr ed,eq⟩
    have := card_le_card sub;omega
  have fixed (c : V→Bool) (cp : ProperOn G (univ\X) c) : allowance G r p A=2 ∧
      (sideNeighbors G a c false).card=2 ∧ (sideNeighbors G a c true).card=2 := by
    have e := sides_sum G a c;have f := bound c cp false;have t := bound c cp true;omega
  obtain ⟨c,cp⟩ := (color_function ..).mp bi
  refine ⟨four,(fixed c cp).1,fun d dp s => ?_⟩
  cases s
  · exact (fixed d dp).2.1
  · exact (fixed d dp).2.2

/-- Two protected tips may choose their colors independently. A failed
marking defeats all four choices, with a shared conflict counted once. -/
theorem double_rigidity (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (a b : V) (ne : a≠b) (ak : a∈A∩insert r (parity G r p)) (bk : b∈A∩insert r (parity G r p))
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (i j : Bool) :
    allowance G r p A < (sideNeighbors G a c i∪sideNeighbors G b c j).card := by
  classical
  let K := A∩insert r (parity G r p)
  let X : Finset V := {a,b}
  let d (v : V) := if v=a then i else j
  have incl : X⊆K := insert_subset ak (singleton_subset_iff.mpr bk)
  have lower := conflict_failure G gc hn r p A X ai bad c d cp
  change allowance G r p A<(X\K).card+(conflicts G (univ\X) (X∩K) c d).card at lower
  rw [sdiff_eq_empty_iff_subset.mpr incl,card_empty,zero_add,inter_eq_left.mpr incl] at lower
  apply lower.trans_le (card_le_card ?_)
  intro y ym
  obtain ⟨x,xm,ed,eq⟩ := (mem_filter.mp ym).2
  rcases mem_insert.mp xm with e|m
  · subst x
    exact mem_union_left _ (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr ed,by simpa [d] using eq⟩)
  · obtain rfl := mem_singleton.mp m
    exact mem_union_right _ (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr ed,by simpa [d,ne.symm] using eq⟩)

#print axioms solo_rigidity
#print axioms double_rigidity
end Minimal180.PairRepair
