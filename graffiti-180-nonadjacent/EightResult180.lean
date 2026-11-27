import EightPair180
import SharedBudget180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals

theorem cover_impossible : ∀ K,¬PairCover G K := by
  have get {a b : V} (ab : a≠b) (mem : ({a,b}:Finset V)∈pairs) : TransPair G a b := ⟨ab,lower_pair _ mem⟩
  exact two_forced_centers G (a:=0) (b:=7) (x:=1) (y:=5) (z:=4) (w:=6) (by decide)
    (get (by decide) (by decide)) (get (by decide) (by decide)) (by decide)
    (get (by decide) (by decide)) (get (by decide) (by decide)) (by decide)

theorem old_criterion_fails : ∀ a b,¬GoodPair G a b := by
  intro a b good
  obtain ⟨ab,bi,law⟩ := good
  have mem := (exact_pairs.2 _ (card_pair ab)).mp bi
  have denied : ∀ i j : V,({i,j}:Finset V)∈pairs → ¬G.Adj i j ∧ (G.degree i=4 ∨ G.degree j=4) := by
    simp only [←card_neighborFinset_eq_degree];decide
  obtain ⟨na,four⟩ := denied a b mem
  obtain ⟨af,bf,_⟩ := law.resolve_left na
  have instDegree (i : V) (F H : Fintype (G.neighborSet i)) :
      @SimpleGraph.degree V G i F=@SimpleGraph.degree V G i H := by rw [Subsingleton.elim F H]
  rcases four with h|h
  · exact af ((instDegree a _ _).trans h)
  · exact bf ((instDegree b _ _).trans h)

private theorem three_steps {a b c d : Bool} (ab : a≠b) (bc : b≠c) (cd : c≠d) : a≠d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem two_steps {a b c : Bool} (ab : a≠b) (bc : b≠c) : a=c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Every successful budget-two witness keeps 5 and changes the relative
colors of 1 and 2. Their old path is 1-4-6-2. Their new path is 1-5-2. -/
theorem recoloring_required (c : V→Bool) (old : ProperOn G (univ\X) c)
    (Z : Finset V) (keep : A⊆Z) (large : 6≤Z.card) (e : V→Bool) (up : ProperOn G Z e) :
    (5:V)∈Z ∧ c 1≠c 2 ∧ e 1=e 2 := by
  have col := (color_function ..).mpr ⟨e,up⟩
  have force := unprotected_retained Z col keep large
  refine ⟨force,three_steps (old 1 (by decide) 4 (by decide) (by decide))
    (old 4 (by decide) 6 (by decide) (by decide)) (old 6 (by decide) 2 (by decide) (by decide)),?_⟩
  exact two_steps (up 1 (keep (by decide)) 5 force (by decide)) (up 5 force 2 (keep (by decide)) (by decide))

theorem all_tests : (∀ r,PrimeTests G r) ∧ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (f : W→V),Bags H G f →
      1+independence H+maxEven H≤maxLeaves H+bipartiteNum H := by
  refine ⟨fun r => protected_tests G r (of_no_cover G data.1 (by decide) cover_impossible r),?_⟩
  intro W _ _ H f h
  exact (cover_substitutions h data.1 (by decide) cover_impossible).2.2

#print axioms cover_impossible
#print axioms old_criterion_fails
#print axioms recoloring_required
#print axioms Eight.all_tests
end Minimal180.PairRepair.Eight
