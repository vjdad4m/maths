import OutwardRank180
import IntersectingPairs180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_outward_single (G : SimpleGraph V) (r x u : V) :
    x∈outward G r {u} ↔ Pred G r x u := by
  classical
  simp only [outward,mem_filter,mem_erase,mem_univ,and_true,mem_singleton,exists_eq_left]
  refine ⟨And.right,fun pr => ⟨?_,pr⟩⟩
  rintro rfl
  have h := pr.2
  rw [dist_self] at h
  omega

noncomputable def Fork (G : SimpleGraph V) (r : V) (Y : Finset V) (v : V) : Prop :=
  v∈Y ∧ 2≤(outward G r {v}).card

/-- In a failed marking at deficit at most three, all marked nonroot
outward forks occur at one distance. Their successor pairs have a common
vertex, or realize exactly the three pairs of a triple. -/
theorem rank_three_forks (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (odd : Bool) (A : Finset V) (ai : Indep G A) (rank : Fintype.card V≤bipartiteNum G+3) :
    let P := parity G r odd
    let Y := (A∪P).erase r
    let F (v : V) := outward G r {v}
    let Q := Fork G r Y
    weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card →
    (∀ v∈Y,(F v).card≤2) ∧
    (∀ u,Q u → ∀ v,Q v → G.dist u r=G.dist v r) ∧
    ((∃ z,∀ u,Q u → z∈F u) ∨ ∃ a b c : V,a≠b ∧ a≠c ∧ b≠c ∧
      (∃ u,Q u ∧ F u={a,b}) ∧ (∃ u,Q u ∧ F u={b,c}) ∧ (∃ u,Q u ∧ F u={a,c}) ∧
      ∀ u,Q u → F u={a,b} ∨ F u={b,c} ∨ F u={a,c}) := by
  classical
  intro P Y F Q bad
  have cap (B : Finset V) (inc : B⊆Y) : (outward G r B).card≤B.card+1 := by
    have := outward_budget G hc hn r two odd A ai bad B inc
    omega
  have one (u : V) (uy : u∈Y) : (F u).card≤2 := by
    have h := cap {u} (singleton_subset_iff.mpr uy)
    simpa [F] using h
  have pairs (u : V) (qu : Q u) : (F u).card=2 := le_antisymm (one u qu.1) qu.2
  have meet (u : V) (qu : Q u) (v : V) (qv : Q v) : (F u∩F v).Nonempty := by
    have h := cap {u,v} (insert_subset qu.1 (singleton_subset_iff.mpr qv.1))
    have eq : outward G r {u,v}=F u∪F v := by
      ext x
      simp only [outward,F,mem_filter,mem_erase,mem_univ,and_true,mem_insert,mem_singleton,
        exists_eq_left,mem_union]
      constructor
      · rintro ⟨xr,y,hy,pr⟩
        rcases hy with rfl|rfl
        · exact Or.inl ⟨xr,pr⟩
        · exact Or.inr ⟨xr,pr⟩
      · rintro (⟨xr,pr⟩|⟨xr,pr⟩)
        · exact ⟨xr,u,Or.inl rfl,pr⟩
        · exact ⟨xr,v,Or.inr rfl,pr⟩
    rw [eq] at h
    have size : ({u,v}:Finset V).card≤2 := by
      by_cases e : u=v
      · simp [e]
      · rw [card_pair e]
    have z := card_union_add_card_inter (F u) (F v)
    rw [pairs u qu,pairs v qv] at z
    apply card_pos.mp
    omega
  refine ⟨one,?_,?_⟩
  · intro u qu v qv
    obtain ⟨x,hx⟩ := meet u qu v qv
    have a := ((mem_outward_single G r x u).mp (mem_inter.mp hx).1).2
    have b := ((mem_outward_single G r x v).mp (mem_inter.mp hx).2).2
    omega
  · by_cases nz : ∃ v,Q v
    · exact intersecting_pairs F Q nz pairs meet
    · exact Or.inl ⟨r,fun u qu => (nz ⟨u,qu⟩).elim⟩

#print axioms mem_outward_single
#print axioms rank_three_forks
end Minimal180.HigherRank
