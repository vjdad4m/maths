import FourLocal28

namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar
open private ThreeChoice.pair_turan from ThreeGeometry33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle in S with another vertex of S adjacent to two of its vertices. -/
def book (S : Finset V) : Prop :=
  ∃ C⊆S,G.IsNClique 3 C ∧ ∃ x∈S\C,2≤nbr G x C

private theorem sparse_cross (Q R : Finset V) (dis : Disjoint Q R)
    (sparse : ∀ v∈R,nbr G v Q≤1) :
    (pairs G (Q∪R)).card≤(pairs G Q).card+(pairs G R).card+R.card := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [pairs]
  | @insert x R out ih =>
    have sub : R⊆insert x R := subset_insert _ _
    have less := ih (dis.mono_right sub) (fun v m => sparse v (sub m))
    have outside : x∉Q := fun xm => disjoint_left.mp dis xm (mem_insert_self ..)
    have spread := card_union_le (Q.filter (G.Adj x)) (R.filter (G.Adj x))
    have sum : nbr G x (Q∪R)≤nbr G x Q+nbr G x R := by simpa only [nbr,filter_union] using spread
    have one := sparse x (mem_insert_self ..)
    have un : Q∪insert x R=insert x (Q∪R) := by ext; simp [or_left_comm]
    rw [un,pairs_insert G (by simp [outside,out]),pairs_insert G out,card_insert_of_not_mem out]
    omega

private def cap (n : ℕ) := if n=3 then 3 else RankTable.cap n 2

/-- Removing a triangle costs at most one crossing edge per remaining vertex
when no pair of triangles shares an edge. The isolated triangle accounts for
the exception at order three. -/
theorem book_bound (S : Finset V) (small : S.card≤9) (no : ¬book G S) :
    (pairs G S).card≤(if S.card=3 then 3 else RankTable.cap S.card 2) := by
  classical
  change (pairs G S).card≤cap S.card
  induction eqZ : S.card using Nat.strong_induction_on generalizing S with
  | h z ih =>
    by_cases tri : ∃ Q⊆S,G.IsNClique 3 Q
    · obtain ⟨Q,sub,qcl⟩ := tri
      let R := S\Q
      have cnt : R.card+3=z := by rw [←qcl.2,show R=S\Q from rfl,card_sdiff_add_card_eq_card sub,eqZ]
      have noR : ¬book G R := by
        rintro ⟨C,cs,cl,x,xm,ed⟩
        exact no ⟨C,cs.trans sdiff_subset,cl,x,mem_sdiff.mpr ⟨sdiff_subset (mem_sdiff.mp xm).1,(mem_sdiff.mp xm).2⟩,ed⟩
      have rem := ih R.card (by omega) R (by omega) noR rfl
      have ed : (pairs G Q).card≤3 := by
        have le := card_filter_le (Q.powersetCard 2) (fun p => ∀ x∈p,∀ y∈p,x≠y → G.Adj x y)
        change (pairs G Q).card≤(Q.powersetCard 2).card at le
        rw [card_powersetCard,qcl.2] at le
        exact le
      have cr := sparse_cross G Q R disjoint_sdiff (fun v vm => Nat.le_of_not_gt
        (fun many => no ⟨Q,sub,qcl,v,vm,many⟩))
      rw [show Q∪R=S from union_sdiff_of_subset sub] at cr
      have tab : ∀ j : Fin 7,3+cap j+j.val≤cap (j.val+3) := by decide
      have step := tab ⟨R.card,by omega⟩
      change 3+cap R.card+R.card≤cap (R.card+3) at step
      rw [cnt] at step
      omega
    · have few := ThreeChoice.pair_turan G S (r:=2) (by decide) (fun Q qs cl => tri ⟨Q,qs,cl⟩)
      have tab := RankTable.cap_table ⟨z,by omega⟩ ⟨2,by decide⟩ (by decide)
      change (turanGraph z 2).edgeFinset.card=RankTable.cap z 2 at tab
      rw [eqZ,tab] at few
      unfold cap
      split_ifs with eq
      · rw [eq] at few; exact few.trans (by decide)
      · exact few

/-- Distinct positive scores allow at most one degree-three center exceeding
the bipartite bound. Every other remote center contains a diamond in its link. -/
theorem remote_book (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (free : G.CliqueFree 5) (half : 14≤gamma G)
    (P : Finset V) (size : P.card∈({1,2}:Finset ℕ))
    (special : P.card=2 → ∃ e,trianglesAt G e=1 ∧ 2≤nbr G e P) :
    ∃ v∈remote G P 9,book G (G.neighborFinset v) := by
  classical
  have many := remote_count G n pos fi free half P size special 9 (by decide)
  by_contra! none
  have score (v : V) (vm : v∈remote G P 9) : trianglesAt G v=3 := by
    obtain ⟨_,_,dg,gt⟩ := (mem_filter.mp vm).2
    have up := book_bound G (G.neighborFinset v) (by simpa using dg) (none v vm)
    rw [card_neighborFinset_eq_degree] at up
    change trianglesAt G v≤_ at up
    split_ifs at up with d
    · rw [d] at gt; have two : RankTable.cap 3 2=2 := by decide
      omega
    · omega
  have one := card_le_one.mpr (fun v vm w wm => fi ((score v vm).trans (score w wm).symm))
  omega
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.book_bound
#print axioms Graffiti384b.Four28.remote_book
