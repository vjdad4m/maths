import MatchedSquare28

namespace Graffiti384b.Sparse28
open Finset SimpleGraph HighEar
open private Four28.sparse_cross from FourDiamond28
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def CommonSparse (S : Finset V) : Prop :=
  ∀ a∈S,∀ b∈S,a≠b → (S.filter (fun z => G.Adj a z ∧ G.Adj b z)).card≤1

omit [Fintype V] [DecidableEq V] in
theorem inherit_sparse {S R : Finset V} (sub : R⊆S) (sparse : CommonSparse G S) : CommonSparse G R := by
  intro a am b bm ne
  exact (card_le_card (filter_subset_filter _ sub)).trans (sparse a (sub am) b (sub bm) ne)

private theorem empty_pairs : (pairs G ∅).card=0 := by
  apply Nat.eq_zero_of_le_zero
  exact (card_filter_le ..).trans (by rw [card_powersetCard,card_empty]; decide)

theorem degree_sum (S : Finset V) : (∑ v∈S,nbr G v S)=2*(pairs G S).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [empty_pairs]
  | @insert w S out ih =>
    have add (v : V) : nbr G v (insert w S)=nbr G v S+(if G.Adj w v then 1 else 0) := by
      by_cases h : G.Adj w v
      · simp [nbr,filter_insert,h,h.symm,out,card_insert_of_not_mem]
      · have rev : ¬G.Adj v w := fun a => h a.symm
        simp [nbr,filter_insert,h,rev]
    rw [sum_insert out,pairs_insert G out]
    simp_rw [add]
    rw [sum_add_distrib,ih,sum_boole]
    simp only [G.irrefl,ite_false,Nat.add_zero]
    change nbr G w S+(2*(pairs G S).card+nbr G w S)=2*((pairs G S).card+nbr G w S)
    omega

def squareCap (n : ℕ) : ℕ := [0,0,1,3,4,6,7,10,12,14,17][n]?.getD 0

private theorem step_table : ∀ n d : Fin 11,0<n.val → d.val<n.val →
    min (n.val*d.val/2) (n.val-1+d.val/2+squareCap (n.val-1-d.val))≤squareCap n.val := by decide

/-- Choose a vertex of maximum degree d. Its neighbors induce at most
d/2 edges, and every other vertex has at most one edge to its neighbors. -/
theorem square_bound (S : Finset V) (small : S.card≤10) (sparse : CommonSparse G S) :
    (pairs G S).card≤squareCap S.card := by
  classical
  induction eqn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases emp : S=∅
    · subst S; rw [empty_pairs]; exact Nat.zero_le _
    obtain ⟨w,wm,big⟩ := exists_max_image S (fun z => nbr G z S) (nonempty_iff_ne_empty.mpr emp)
    let A := S.filter (G.Adj w)
    let R := S.erase w\A
    have sub : A⊆S.erase w := fun z zm => mem_erase.mpr ⟨(mem_filter.mp zm).2.ne.symm,(mem_filter.mp zm).1⟩
    have size : R.card=n-1-A.card := by rw [show R=S.erase w\A from rfl,card_sdiff sub,card_erase_of_mem wm,eqn]
    have dsmall := card_le_card sub
    rw [card_erase_of_mem wm,eqn] at dsmall
    have pos : 0<n := eqn ▸ card_pos.mpr ⟨w,wm⟩
    have coarse := sum_le_sum (s:=S) (fun z zm => big z zm)
    rw [Sparse28.degree_sum,sum_const,nsmul_eq_mul,eqn] at coarse
    change 2*(pairs G S).card≤n*A.card at coarse
    have near {z : V} (zm : z∈S) (zw : z≠w) : nbr G z A≤1 := by
      have val := sparse w wm z zm zw.symm
      simpa only [nbr,A,filter_filter] using val
    have internal := sum_le_sum (s:=A) (fun z zm => near (mem_filter.mp zm).1 (mem_filter.mp zm).2.ne.symm)
    rw [Sparse28.degree_sum,sum_const,nsmul_eq_mul,mul_one] at internal
    change 2*(pairs G A).card≤A.card at internal
    have rs : R⊆S := sdiff_subset.trans (erase_subset ..)
    have rem := ih R.card (by omega) R (by omega) (inherit_sparse G rs sparse) rfl
    have cr := Four28.sparse_cross G A R disjoint_sdiff (fun z zm =>
      near (rs zm) (mem_erase.mp (mem_sdiff.mp zm).1).1)
    have eq : A∪R=S.erase w := union_sdiff_of_subset sub
    rw [eq] at cr
    have wA : nbr G w (S.erase w)=A.card := by
      change ((S.erase w).filter (G.Adj w)).card=(S.filter (G.Adj w)).card
      congr 1; ext z; simp only [mem_filter,mem_erase]; constructor
      · exact fun h => ⟨h.1.2,h.2⟩
      · exact fun h => ⟨⟨h.2.ne.symm,h.1⟩,h.2⟩
    have ins := pairs_insert G (not_mem_erase w S)
    rw [insert_erase wm,wA] at ins
    change (pairs G S).card=(pairs G (S.erase w)).card+A.card at ins
    rw [size] at rem cr
    have cover : n-1-A.card+A.card=n-1 := Nat.sub_add_cancel dsmall
    have low : (pairs G S).card≤min (n*A.card/2) (n-1+A.card/2+squareCap (n-1-A.card)) := by
      apply le_min <;> omega
    exact low.trans (step_table ⟨n,by omega⟩ ⟨A.card,by omega⟩ pos (show A.card<n by omega))

end Graffiti384b.Sparse28
#print axioms Graffiti384b.Sparse28.degree_sum
#print axioms Graffiti384b.Sparse28.square_bound
