import PortRecurrence180
import WitnessExtension180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Compute the restored bipartite order using only old maximum
two-color witnesses. -/
noncomputable def restoredB (G : SimpleGraph V) (N : Finset V) : ℕ := by
  classical exact bipartiteNum G + if ∃ C D,Indep G C ∧ Indep G D ∧ Disjoint C D ∧
    C.card+D.card=bipartiteNum G ∧ Disjoint C N then 1 else 0

theorem restored_bipartite (G : SimpleGraph V) (N : Finset V) :
    bipartiteNum (ear G N)=restoredB G N := by
  classical
  obtain ⟨X,col,opt⟩ := optB (ear G N)
  have rest := restrict_color G (ear G N) Sum.inl Sum.inl_injective (fun e => e) col
  have cap := size_bip G rest
  have cnt := congrArg card (present X)
  rw [card_lift] at cnt
  have bit : (decide (Sum.inr ()∈X)).toNat≤1 := by cases decide (Sum.inr ()∈X) <;> decide
  have low := rank_mono G N
  have iff := color_gain_iff G N
  unfold restoredB
  split_ifs with hit
  · have := iff.mpr hit; omega
  · have := mt iff.mp hit; omega

omit [Fintype V] [DecidableEq V] in
theorem independent_lift_iff (G : SimpleGraph V) (N A : Finset V) (a : Bool) :
    Indep (ear G N) (lift A a) ↔ Indep G A ∧ (a=true → Disjoint A N) := by
  constructor
  · intro ok
    refine ⟨fun x hx y hy ne e => ok _ ((inl_lift ..).mpr hx) _ ((inl_lift ..).mpr hy)
      (fun eq => ne (Sum.inl.inj eq)) e,?_⟩
    intro on
    apply disjoint_left.mpr
    intro x xa xn
    exact ok (.inl x) ((inl_lift ..).mpr xa) (.inr ()) ((inr_lift ..).mpr on) (fun e => Sum.noConfusion e) xn
  · rintro ⟨old,clean⟩ (x|u) hx (y|w) hy ne edge
    · exact old x ((inl_lift ..).mp hx) y ((inl_lift ..).mp hy) (fun e => ne (congrArg Sum.inl e)) edge
    · exact disjoint_left.mp (clean ((inr_lift ..).mp hy)) ((inl_lift ..).mp hx) edge
    · exact disjoint_left.mp (clean ((inr_lift ..).mp hx)) ((inl_lift ..).mp hy) edge
    · exact edge.elim

/-- Exact criterion for the entire local bound at the restored root,
with both graph invariants, all independent markings, and the target
expressed on the smaller graph alone. -/
theorem deleted_root_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (degree : 1<N.card) (p : Bool) :
    let nz : N.Nonempty := card_pos.mp (by omega)
    let P := nearParity G N nz (!p)
    localBound (ear G N) (.inr ()) (parity (ear G N) (.inr ()) p) ↔
      ∀ A : Finset V, ∀ a : Bool, Indep G A → (a=true → Disjoint A N) →
        let U := A∪P
        let t := 1+A.card+a.toNat+P.card+(!p).toNat-restoredB G N
        (∃ S⊆U,t≤S.card ∧ AllowsLeaves G N S) ∨
        ∃ x∈N,t≤weightedLeaves G (U.erase x)+(a && !p).toNat := by
  classical
  intro nz P
  constructor
  · intro bound A a ind clean
    have test := (rooted_old_tests G gc hn N degree A a p).mp (bound _ ((independent_lift_iff ..).mpr ⟨ind,clean⟩))
    simpa only [restored_bipartite] using test
  · intro tests B independent
    let A := pull Sum.inl B
    let a := decide (Sum.inr ()∈B)
    have rep : B=lift A a := present B
    rw [rep] at independent ⊢
    have ⟨ind,clean⟩ := (independent_lift_iff ..).mp independent
    apply (rooted_old_tests G gc hn N degree A a p).mpr
    simpa only [restored_bipartite] using tests A a ind clean

#print axioms restored_bipartite
#print axioms independent_lift_iff
#print axioms deleted_root_iff
end Minimal180.PortParity
