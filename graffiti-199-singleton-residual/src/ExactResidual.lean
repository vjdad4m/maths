import RootExtension
import PortMiss

namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Existence of a separating three-set at exact connectivity three. -/
theorem separating_three_at_exact_three (order : 5 ≤ Fintype.card V) (k : vertexConnectivity G = 3) :
    ∃ D : Finset V, D.card = 3 ∧ ¬ (DeletionGraph G D).Preconnected := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have conn : ConnectivityAtLeast G 3 := k ▸ connectivityAtLeast_vertexConnectivity
  by_contra! all
  have four : ConnectivityAtLeast G 4 := by
    refine ⟨by omega,fun D small => ?_⟩
    by_cases few : D.card < 3
    · exact conn.2 D few
    have proper : D.card < (Finset.univ : Finset V).card := by rw [Finset.card_univ]; omega
    obtain ⟨v,_,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card proper
    exact @SimpleGraph.Connected.mk _ (DeletionGraph G D) (all D (by omega)) ⟨⟨v,off⟩⟩
  have lo : 4 ≤ vertexConnectivity G := Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr four.1,four⟩)
  omega

/-- The three vertices other than the root belong to the connected ordinary shore.
Every selected quartet has the stated contact restrictions. -/
def SaturatedPort (G : SimpleGraph V) [DecidableEq V] (X : Set V) (r a b : V) : Prop :=
  (∃ f : Fin 4 ↪ V, f 0 = r ∧ (∀ i, i ≠ 0 → f i ∈ X) ∧ RootOrdering G f) ∧
  (∀ f : Fin 5 ↪ V, f 0 = r → (∀ i, i ≠ 0 → f i ∈ X) → ¬ RootOrdering G f) ∧
  ∀ f : Fin 4 ↪ V, f 0 = r → (∀ i, i ≠ 0 → f i ∈ X) → RootOrdering G f →
    (∀ w ∈ X, (∀ i, w ≠ f i) → ∀ i, G.Adj w (f i) → ∃ j, i ≠ j ∧ G.Adj w (f j)) ∧
    (∀ p ∈ ({a,b} : Finset V), ∃ i, G.Adj p (f i))

/-- Every actual separating triple has this profile; no attachment or
path data is supplied in the hypotheses. -/
theorem catalogue_minimum_singleton_profile
    (minimum : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), Fintype.card W < Fintype.card V →
      H.Connected → 2 ≤ Fintype.card W → treeNumber H ≤ vertexConnectivity H + 2 → Traceable H)
    (k : vertexConnectivity G = 3) (bound : treeNumber G ≤ vertexConnectivity G + 2)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ u v, G.degree u = 3 → G.degree v = 3 → ¬ G.Adj u v) :
    (∃ D : Finset V, D.card = 3 ∧ ¬ (DeletionGraph G D).Preconnected) ∧
    ∀ D : Finset V, D.card = 3 → ¬ (DeletionGraph G D).Preconnected →
      ∃ z : V, ∃ X : Set V, Nonempty (PathOn G {v | v ≠ z}) ∧
        ∀ r a b : V, r ≠ a → r ≠ b → a ≠ b → D = {r,a,b} →
          SingletonCut G X z r a b ∧ SaturatedPort G X r a b ∧
          (∃ W : Finset V, W.card = 4 ∧ (∀ w ∈ W, w ∈ X) ∧
            (∀ x ∈ W, ∀ y ∈ W, ¬ G.Adj x y) ∧ ∀ s ∈ D, ∃ w ∈ W, ¬ G.Adj s w) ∧
          ∀ s ∈ D, (∃ v ∈ X, ¬ G.Adj s v ∧ ∃ t ∈ D, t ≠ s ∧ G.Adj t v) ∨
            ∀ P : PathOn G {v | v ≠ z}, P.first ≠ P.last ∧ ¬ G.Adj s P.first ∧ ¬ G.Adj s P.last := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have conn : ConnectivityAtLeast G 3 := k ▸ connectivityAtLeast_vertexConnectivity
  have budget : treeNumber G ≤ 5 := by omega
  have smaller := smallerAtThree_of_catalogue_minimum minimum
  refine ⟨separating_three_at_exact_three order k,?_⟩
  intro D size cut
  obtain ⟨z,X,frame⟩ := all_ports_have_rooted_four smaller conn budget order no ind size cut
  obtain ⟨r,a,b,ra,rb,ab,ed⟩ := Finset.card_eq_three.mp size
  have F := (frame r a b ra rb ab ed).1
  obtain ⟨P⟩ := pathOn_of_traceable_delete
    (traceable_after_cubic_delete smaller conn budget order no ind F.cubic)
  refine ⟨z,X,⟨P⟩,?_⟩
  intro s t u st su tu eq
  obtain ⟨B,witness⟩ := frame s t u st su tu eq
  refine ⟨B,⟨witness,B.no_rooted_five,fun f head side root => B.quartet_contacts f head side root⟩,
    ⟨P.terminalQuartet,by rw [P.terminalQuartet_card no,F.cubic],B.flanks_in_shore no P,
      P.terminalQuartet_independent no,fun v hv => B.misses_flank no P (eq ▸ hv)⟩,?_⟩
  rw [eq]
  exact fun v hv => B.port_miss_dichotomy no hv

#print axioms separating_three_at_exact_three
#print axioms catalogue_minimum_singleton_profile
end Graffiti199Depleted.Catalogue.Incomplete

