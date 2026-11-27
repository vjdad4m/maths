import PruneMarks180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

def BadMark (H : SimpleGraph V) (r : V) (p : Bool) (A : Finset V) : Prop :=
  weightedLeaves H (eligible A (parity H r p) r)+bipartiteNum H<1+A.card+(parity H r p).card

/-- A nonroot vertex with a surviving bag mate is necessarily doubly
marked in any offending marking of an induced-minimal failed graph. -/
theorem Bags.minimal_marks (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (min : ProperSidesGood H) (r x y : V) (xr : x≠r) (xy : x≠y) (mate : f x=f y)
    (p : Bool) (A : Finset V) (ai : Indep H A) (bad : BadMark H r p A) : x∈A∩parity H r p := by
  classical
  by_contra no
  let S := univ.erase x
  have keep (i : B) : ∃ v∈S,f v=i := by
    obtain ⟨v,vi⟩ := h.onto i
    by_cases eq : v=x
    · exact ⟨y,mem_erase.mpr ⟨xy.symm,mem_univ _⟩,mate.symm.trans (eq ▸ vi)⟩
    · exact ⟨v,mem_erase.mpr ⟨eq,mem_univ _⟩,vi⟩
  have all : A∩parity H r p⊆S := fun v m => mem_erase.mpr ⟨fun eq => no (eq ▸ m),mem_univ _⟩
  let rr : ↥S := ⟨r,mem_erase.mpr ⟨xr.symm,mem_univ _⟩⟩
  have ⟨ind,fail⟩ := h.prune H G f gc hn S keep rr p A ai all bad
  have ret := h.retained S keep
  have big := Fintype.card_le_of_surjective _ ret.onto
  change Fintype.card B≤Fintype.card ↥S at big
  rw [Fintype.card_coe] at big
  have smaller : S.card<Fintype.card V := by
    have := card_erase_add_one (mem_univ x)
    change (univ.erase x).card<Fintype.card V
    rw [card_univ] at this; omega
  exact (Nat.not_lt_of_ge (min S smaller (by omega) (ret.connected gc hn) rr p _ ind)) fail

theorem members_same (M : Finset V) (a x y : V) (xm : x∈M) (ym : y∈M) :
    collapse M a x=collapse M a y := Subtype.ext (by simp [collapse_val,xm,ym])

/-- Away from the root, every nontrivial proper module consists of
doubly marked independent vertices. In the root module, adjacency
to the root is determined exactly by the chosen parity. -/
theorem minimal_shape (H : SimpleGraph V) (hc : H.Connected) (min : ProperSidesGood H)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep H A) (bad : BadMark H r p A)
    (M : Finset V) (hom : Homogeneous H M) (fat : 1<M.card) (proper : M≠univ) :
    (∀ x∈M,x≠r → x∈A∩parity H r p) ∧ Indep H (M.erase r) ∧
    (r∈M → ∀ x∈M,x≠r → (H.Adj x r ↔ p=true)) := by
  classical
  obtain ⟨a,am⟩ := card_pos.mp (show 0<M.card by omega)
  let J := side H (reps M a)
  let f := collapse M a
  have h := module_bags H M hom a am
  have jc := quotient_connected H hc M hom a am
  have order := (quotient_order M a am fat proper).1
  have marked (x : V) (xm : x∈M) (xr : x≠r) : x∈A∩parity H r p := by
    obtain ⟨y,ym,yx⟩ := exists_ne_of_one_lt_card fat x
    exact h.minimal_marks jc order min r x y xr yx.symm (members_same M a x y xm ym) p A ai bad
  refine ⟨marked,fun x xm y ym => ai x (mem_inter.mp (marked _ (mem_erase.mp xm).2 (mem_erase.mp xm).1)).1
    y (mem_inter.mp (marked _ (mem_erase.mp ym).2 (mem_erase.mp ym).1)).1,?_⟩
  intro rm x xm xr
  have m := (mem_parity H r x p).mp (mem_inter.mp (marked x xm xr)).2
  have d := h.metric jc order x r
  have eq := members_same M a x r xm rm
  constructor
  · intro e
    rw [dist_eq_one_iff_adj.mpr e] at m
    cases p <;> simp_all
  · rintro rfl
    by_contra ne
    have two : H.dist x r=2 := by simpa [eq,xr,ne] using d
    simp [two] at m

/-- Clique modules cannot occur at any boundary degree. -/
theorem minimal_nonclique (H : SimpleGraph V) (hc : H.Connected) (min : ProperSidesGood H)
    (r : V) (p : Bool) (bad : ¬localBound H r (parity H r p))
    (M : Finset V) (hom : Homogeneous H M) (fat : 1<M.card) (proper : M≠univ) :
    ∃ x∈M,∃ y∈M,x≠y ∧ ¬H.Adj x y := by
  classical
  by_contra! clique
  obtain ⟨a,am⟩ := card_pos.mp (show 0<M.card by omega)
  let J := side H (reps M a)
  let f := collapse M a
  have bags := module_bags H M hom a am
  have jc := quotient_connected H hc M hom a am
  obtain ⟨order,smaller⟩ := quotient_order M a am fat proper
  have low : localBound J (f r) (parity J (f r) p) :=
    min _ (by simpa only [Fintype.card_coe] using smaller) (by simpa only [Fintype.card_coe] using order) jc _ _
  apply bad (bags.rooted (cover_cliques H J f ?_) jc order r p low)
  intro x y eq ne
  have vals := congrArg Subtype.val eq
  change (collapse M a x).val=(collapse M a y).val at vals
  rw [collapse_val,collapse_val] at vals
  by_cases xm : x∈M <;> by_cases ym : y∈M <;> simp [xm,ym] at vals
  · exact clique x xm y ym ne
  · exact (ym (vals ▸ am)).elim
  · exact (xm (vals.symm ▸ am)).elim
  · exact (ne vals).elim

#print axioms Bags.minimal_marks
#print axioms minimal_shape
#print axioms minimal_nonclique
end Minimal180.Substitution
