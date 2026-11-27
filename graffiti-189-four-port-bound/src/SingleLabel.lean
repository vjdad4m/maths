import RankLabels

namespace Graffiti189SingletonCage
open GraphPathLift Finset SimpleGraph
open Graffiti189LongestPath.FourCut.Three
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {r a b : V}
variable (S : SingleRoot G r a b)

def exclusiveA : Finset V := S.ports.filter (fun v=>G.Adj a v ∧ ¬G.Adj b v)
def exclusiveB : Finset V := S.ports.filter (fun v=>G.Adj b v ∧ ¬G.Adj a v)

def rootRank (_ : SingleRoot G r a b) (v : V) : ℕ :=
  if v=r then 0 else if v=a then 1 else if v=b then 2
  else if G.Adj a v then (if G.Adj b v then 5 else 3)
  else if G.Adj b v then 4 else 6

lemma rank_zero (v : V) : rootRank S v=0 ↔ v=r := by
  by_cases hr : v=r
  · subst v; simp [rootRank,S.left.ne,S.right.ne]
  by_cases ha : v=a
  · subst v; simp [rootRank,S.left.ne.symm,S.ab]
  by_cases hb : v=b
  · subst v; simp [rootRank,S.right.ne.symm,S.ab.symm]
  by_cases ea : G.Adj a v <;> by_cases eb : G.Adj b v <;>
    simp [rootRank,hr,ha,hb,ea,eb]

lemma rank_one (v : V) : rootRank S v=1 ↔ v=a := by
  by_cases hr : v=r
  · subst v; simp [rootRank,S.left.ne,S.right.ne]
  by_cases ha : v=a
  · subst v; simp [rootRank,S.left.ne.symm,S.ab]
  by_cases hb : v=b
  · subst v; simp [rootRank,S.right.ne.symm,S.ab.symm]
  by_cases ea : G.Adj a v <;> by_cases eb : G.Adj b v <;>
    simp [rootRank,hr,ha,hb,ea,eb]

lemma rank_two (v : V) : rootRank S v=2 ↔ v=b := by
  by_cases hr : v=r
  · subst v; simp [rootRank,S.left.ne,S.right.ne]
  by_cases ha : v=a
  · subst v; simp [rootRank,S.left.ne.symm,S.ab]
  by_cases hb : v=b
  · subst v; simp [rootRank,S.right.ne.symm,S.ab.symm]
  by_cases ea : G.Adj a v <;> by_cases eb : G.Adj b v <;>
    simp [rootRank,hr,ha,hb,ea,eb]

lemma rank_three (v : V) : rootRank S v=3 ↔ v∈exclusiveA S := by
  unfold exclusiveA SingleRoot.ports
  simp only [mem_filter, S.mem_off3]
  by_cases hr : v=r
  · subst v; simp [rootRank,S.left.ne,S.right.ne]
  by_cases ha : v=a
  · subst v; simp [rootRank,S.left.ne.symm,S.ab]
  by_cases hb : v=b
  · subst v; simp [rootRank,S.right.ne.symm,S.ab.symm]
  by_cases ea : G.Adj a v <;> by_cases eb : G.Adj b v <;>
    simp [rootRank,hr,ha,hb,ea,eb]

lemma rank_four (v : V) : rootRank S v=4 ↔ v∈exclusiveB S := by
  unfold exclusiveB SingleRoot.ports
  simp only [mem_filter, S.mem_off3]
  by_cases hr : v=r
  · subst v; simp [rootRank,S.left.ne,S.right.ne]
  by_cases ha : v=a
  · subst v; simp [rootRank,S.left.ne.symm,S.ab]
  by_cases hb : v=b
  · subst v; simp [rootRank,S.right.ne.symm,S.ab.symm]
  by_cases ea : G.Adj a v <;> by_cases eb : G.Adj b v <;>
    simp [rootRank,hr,ha,hb,ea,eb]

lemma rank_lt_six (v : V) : rootRank S v<6 ↔ v=r ∨ v=a ∨ v=b ∨ v∈S.ports := by
  unfold SingleRoot.ports
  simp only [mem_filter, S.mem_off3]
  by_cases hr : v=r
  · subst v; simp [rootRank,S.left.ne,S.right.ne]
  by_cases ha : v=a
  · subst v; simp [rootRank,S.left.ne.symm,S.ab]
  by_cases hb : v=b
  · subst v; simp [rootRank,S.right.ne.symm,S.ab.symm]
  by_cases ea : G.Adj a v <;> by_cases eb : G.Adj b v <;>
    simp [rootRank,hr,ha,hb,ea,eb]

lemma count_rank_one :
    (univ.filter (fun v=>rootRank S v<1)).card=1 := by
  have e : (univ.filter (fun v=>rootRank S v<1)) = ({r}:Finset V) := by
    ext v; simp only [mem_filter,mem_univ,true_and,mem_singleton]
    rw [Nat.lt_one_iff,rank_zero S]
  rw [e,card_singleton]

lemma count_rank_two :
    (univ.filter (fun v=>rootRank S v<2)).card=2 := by
  have e : (univ.filter (fun v=>rootRank S v<2)) = ({r,a}:Finset V) := by
    ext v; simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    rw [←rank_zero S v,←rank_one S v]
    omega
  rw [e,card_insert_of_not_mem (by simp [S.left.ne]),card_singleton]

lemma count_rank_three :
    (univ.filter (fun v=>rootRank S v<3)).card=3 := by
  have e : (univ.filter (fun v=>rootRank S v<3)) = ({r,a,b}:Finset V) := by
    ext v; simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    rw [←rank_zero S v,←rank_one S v,←rank_two S v]
    omega
  rw [e,card_insert_of_not_mem (by simp [S.left.ne,S.right.ne]),
    card_insert_of_not_mem (by simp [S.ab]),card_singleton]

lemma count_rank_four :
    (univ.filter (fun v=>rootRank S v<4)).card=3+(exclusiveA S).card := by
  let P : Finset V := univ.filter (fun v=>rootRank S v<3)
  have es : (univ.filter (fun v=>rootRank S v<4)) = P∪exclusiveA S := by
    ext v; simp only [mem_filter,mem_univ,true_and,mem_union,P]
    rw [←rank_three S v]; omega
  have dis : Disjoint P (exclusiveA S) := disjoint_left.mpr (fun v hv hr => by
    have a := (mem_filter.mp hv).2
    have b := (rank_three S v).mpr hr
    omega)
  rw [es,card_union_of_disjoint dis,show P.card=3 from count_rank_three S]

lemma count_rank_five :
    (univ.filter (fun v=>rootRank S v<5)).card=3+(exclusiveA S).card+(exclusiveB S).card := by
  let P : Finset V := univ.filter (fun v=>rootRank S v<4)
  have es : (univ.filter (fun v=>rootRank S v<5)) = P∪exclusiveB S := by
    ext v; simp only [mem_filter,mem_univ,true_and,mem_union,P]
    rw [←rank_four S v]; omega
  have dis : Disjoint P (exclusiveB S) := disjoint_left.mpr (fun v hv hr => by
    have a := (mem_filter.mp hv).2
    have b := (rank_four S v).mpr hr
    omega)
  rw [es,card_union_of_disjoint dis,show P.card=3+(exclusiveA S).card from count_rank_four S]

lemma count_rank_six (four : S.ports.card=4) :
    (univ.filter (fun v=>rootRank S v<6)).card=7 := by
  have e : (univ.filter (fun v=>rootRank S v<6)) = ({r,a,b}:Finset V) ∪ S.ports := by
    ext v; simp [rank_lt_six S, or_assoc]
  have dis : Disjoint ({r,a,b}:Finset V) S.ports := disjoint_left.mpr (fun v h hp=>by
    have ⟨nr,na,nb⟩ := S.mem_off3.mp (mem_filter.mp hp).1
    simp only [mem_insert,mem_singleton] at h
    exact h.elim nr (fun h=>h.elim na nb))
  rw [e,card_union_of_disjoint dis,four,card_insert_of_not_mem (by simp [S.left.ne,S.right.ne]),
    card_insert_of_not_mem (by simp [S.ab]),card_singleton]

lemma positions (four : S.ports.card=4) (e : Fin (Fintype.card V) ≃ V)
    (mono : Monotone (rootRank S ∘ e)) (i : Fin (Fintype.card V)) :
    rootRank S (e i) =
      if i.val=0 then 0 else if i.val=1 then 1 else if i.val=2 then 2 else
      if i.val<3+(exclusiveA S).card then 3 else
      if i.val<3+(exclusiveA S).card+(exclusiveB S).card then 4 else
      if i.val<7 then 5 else 6 := by
  have h1 := rank_cut_iff (rootRank S) e mono i 1
  have h2 := rank_cut_iff (rootRank S) e mono i 2
  have h3 := rank_cut_iff (rootRank S) e mono i 3
  have h4 := rank_cut_iff (rootRank S) e mono i 4
  have h5 := rank_cut_iff (rootRank S) e mono i 5
  have h6 := rank_cut_iff (rootRank S) e mono i 6
  rw [count_rank_one S] at h1
  rw [count_rank_two S] at h2
  rw [count_rank_three S] at h3
  rw [count_rank_four S] at h4
  rw [count_rank_five S] at h5
  rw [count_rank_six S four] at h6
  have ub : rootRank S (e i)≤6 := by unfold rootRank; split_ifs <;> omega
  split_ifs <;> omega

theorem exists_numbering (four : S.ports.card=4) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      (∀ i, e i=r ↔ i.val=0) ∧
      ∀ i j p, i<j →
        wanted (exclusiveA S).card (exclusiveB S).card (decide (G.Adj a b)) i j=some p →
        decide (G.Adj (e i) (e j))=p := by
  obtain ⟨e,mono⟩ := exists_sorted_equiv (rootRank S)
  have rank := positions S four e mono
  have rst (i : Fin (Fintype.card V)) : e i=r ↔ i.val=0 := by
    rw [←rank_zero S,rank]
    split_ifs <;> simp_all
  have fst (i : Fin (Fintype.card V)) : e i=a ↔ i.val=1 := by
    rw [←rank_one S,rank]
    split_ifs <;> simp_all
  have snd (i : Fin (Fintype.card V)) : e i=b ↔ i.val=2 := by
    rw [←rank_two S,rank]
    split_ifs <;> simp_all
  refine ⟨e,rst,?_⟩
  intro i j p ij w
  unfold wanted at w
  by_cases ir : i.val=0
  · simp only [ir,if_true,Option.some.injEq] at w
    rw [←w,(rst i).mpr ir]
    by_cases h : j.val=1 ∨ j.val=2
    · rcases h with h|h
      · rw [(fst j).mpr h]; simp [h,S.left]
      · rw [(snd j).mpr h]; simp [h,S.right]
    · have no : ¬G.Adj r (e j) := fun g=>h ((S.only _ g).elim
        (fun e=>Or.inl ((fst j).mp e)) (fun e=>Or.inr ((snd j).mp e)))
      simp [h,no]
  simp only [ir,if_false] at w
  by_cases eqab : i.val=1 ∧ j.val=2
  · simp [eqab.1,eqab.2,ir] at w
    rw [←w,(fst i).mpr eqab.1,(snd j).mpr eqab.2]
  simp only [eqab,if_false] at w
  by_cases piece : i.val=1 ∨ i.val=2
  · simp only [piece,if_true,Option.some.injEq] at w
    rw [←w]
    have j3 : 3≤j.val := by
      have lt : i.val<j.val := ij
      rcases piece with h|h <;> omega
    have jr : e j≠r := fun g=>by have := (rst j).mp g; omega
    have ja : e j≠a := fun g=>by have := (fst j).mp g; omega
    have jb : e j≠b := fun g=>by have := (snd j).mp g; omega
    have R := rank j
    let code : ℕ :=
      if j.val<3+(exclusiveA S).card then 1
      else if j.val<3+(exclusiveA S).card+(exclusiveB S).card then 2
      else if j.val<7 then 3 else 0
    change decide (G.Adj (e i) (e j)) = decide (code=i.val ∨ code=3)
    have hcode : code = if G.Adj a (e j) then (if G.Adj b (e j) then 3 else 1)
        else if G.Adj b (e j) then 2 else 0 := by
      simp only [rootRank,jr,ja,jb,if_false,show j.val≠0 from by omega,
        show j.val≠1 from by omega, show j.val≠2 from by omega] at R
      dsimp [code]
      split_ifs at R ⊢ <;> omega
    rw [hcode]
    rcases piece with hi|hi
    · rw [(fst i).mpr hi]
      by_cases ea : G.Adj a (e j) <;> by_cases eb : G.Adj b (e j) <;> simp [ea,eb,hi]
    · rw [(snd i).mpr hi]
      by_cases ea : G.Adj a (e j) <;> by_cases eb : G.Adj b (e j) <;> simp [ea,eb,hi]
  simp [piece] at w

#print axioms exists_numbering
#print axioms count_rank_six
end Graffiti189SingletonCage
