import PortComponents180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def AllowsLeaves (G : SimpleGraph V) (N S : Finset V) : Prop :=
  PortComponents G N (univ\S) ∧ ∀ v∈S,v∈N ∨ Dominates G (univ\S) v

/-- The unmarked-apex branch can be evaluated entirely in the deletion
graph. The retained old vertices may have several components. -/
theorem star_core_score (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (N U : Finset V) (nz : N.Nonempty) (t : ℕ) :
    t≤weightedLeaves (ear G N) (lift U false) ↔ ∃ S⊆U,t≤S.card ∧ AllowsLeaves G N S := by
  classical
  let H := ear G N
  have high : 2<Fintype.card (V⊕Unit) := by simp [Fintype.card_sum]; omega
  have cmp (S : Finset V) : (univ\lift S false : Finset (V⊕Unit))=lift (univ\S) true := by
    ext z; rcases z with z|⟨⟩ <;> simp
  rw [score_iff_core _ (ear_connected G gc N nz) high]
  constructor
  · rintro ⟨C,inc,mass,con,dom⟩
    let S := pull Sum.inl C
    have nr : Sum.inr ()∉C := fun h => (by simpa using inc h : False)
    have eq : C=lift S false := by simpa only [decide_eq_false nr] using present C
    rw [eq,card_lift,Bool.toNat_false,add_zero] at mass
    rw [eq,cmp] at con dom
    refine ⟨S,fun v m => (inl_lift ..).mp (inc (mem_pull.mp m)),mass,(con_lift_iff ..).mp con,?_⟩
    intro v vs
    exact (dominates_lift ..).mp (dom (.inl v) ((inl_lift ..).mpr vs))
  · rintro ⟨S,inc,mass,con,dom⟩
    refine ⟨lift S false,?_,by simpa using mass,?_,?_⟩
    · rintro (v|⟨⟩) h
      · exact (inl_lift ..).mpr (inc ((inl_lift ..).mp h))
      · simp at h
    · rw [cmp]; exact (con_lift_iff ..).mpr con
    · rw [cmp]
      rintro (v|⟨⟩) h
      · exact (dominates_lift ..).mpr (dom v ((inl_lift ..).mp h))
      · simp at h

/-- Exact recurrence for the original unrestricted eligible-leaf optimum.
Both alternatives now use only the deletion graph G and its port set. -/
theorem old_graph_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (neighbors : 1<N.card) (e : Bool) (t : ℕ) :
    t≤weightedLeaves (ear G N) (lift U e) ↔
      (∃ S⊆U,t≤S.card ∧ AllowsLeaves G N S) ∨
      ∃ x∈N,t≤weightedLeaves G (U.erase x)+e.toNat := by
  classical
  have nz : N.Nonempty := card_pos.mp (by omega)
  let F (x : V) := weightedLeaves G (U.erase x)
  obtain ⟨w,wn,eq⟩ := exists_mem_eq_sup (s:=N) (f:=F) nz
  rw [apex_score G gc hn N U neighbors e,le_max_iff,star_core_score G gc (by omega) N U nz t]
  apply or_congr_right
  constructor
  · intro ok; exact ⟨w,wn,by change t≤F w+e.toNat; rw [← eq]; exact ok⟩
  · rintro ⟨x,xn,ok⟩; exact ok.trans (Nat.add_le_add_right (le_sup (f:=F) xn) _)

/-- The marked Graffiti.pc 180 inequality at the restored root, with its
true distance parity, is exactly the disjunction of two old-graph tests. -/
theorem rooted_old_tests (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (neighbors : 1<N.card) (A : Finset V) (a p : Bool) :
    let H := ear G N
    let B := lift A a
    let P := parity H (.inr ()) p
    let nz : N.Nonempty := card_pos.mp (by omega)
    let U := A∪nearParity G N nz (!p)
    let t := 1+A.card+a.toNat+(nearParity G N nz (!p)).card+(!p).toNat-bipartiteNum H
    1+B.card+P.card≤weightedLeaves H (eligible B P (.inr ()))+bipartiteNum H ↔
      (∃ S⊆U,t≤S.card ∧ AllowsLeaves G N S) ∨
      ∃ x∈N,t≤weightedLeaves G (U.erase x)+(a && !p).toNat := by
  classical
  intro H B P nz U t
  rw [←old_graph_iff G gc hn N U neighbors (a && !p) t]
  have pp : P=lift (nearParity G N nz (!p)) (!p) := apex_parity G gc N nz p
  rw [pp,apex_eligible,card_lift,card_lift]
  change 1+(A.card+a.toNat)+((nearParity G N nz (!p)).card+(!p).toNat)≤
      weightedLeaves H (lift U (a && !p))+bipartiteNum H ↔ t≤weightedLeaves H (lift U (a && !p))
  dsimp only [t]
  omega

#print axioms star_core_score
#print axioms old_graph_iff
#print axioms rooted_old_tests
end Minimal180.PortParity
