import ExactResidual
import DoubleMissSplice

namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X : Set V} {z r a b : V}

def MissesTwo (G : SimpleGraph V) (X : Set V) (s : V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ ¬ G.Adj s x ∧ ¬ G.Adj s y

private theorem unique_of_not_two (F : SingletonCut G X z r a b) (no : ¬ Traceable G)
    (P : PathOn G {v | v ≠ z}) (h : ¬ MissesTwo G X r) : ∃ x ∈ X, ¬ G.Adj r x ∧
    ∀ w ∈ X, ¬ G.Adj r w → w = x := by
  obtain ⟨x,mem,xr⟩ := F.misses_flank no P (Finset.mem_insert_self r _)
  have xX := F.flanks_in_shore no P x mem
  exact ⟨x,xX,xr,fun w wX off => Classical.byContradiction fun e => h ⟨w,wX,x,xX,e,off,xr⟩⟩

/-- For every pair of distinct ports, one has at least two ordinary nonneighbors.
A port with only one nonneighbor forces a second cubic vertex. -/
theorem SingletonCut.port_pair_profile (F : SingletonCut G X z r a b) (no : ¬ Traceable G)
    (P : PathOn G {v | v ≠ z}) :
    (MissesTwo G X r ∨ MissesTwo G X a) ∧
    (¬ MissesTwo G X r → ∃ x ∈ X, ¬ G.Adj r x ∧ G.degree x = 3 ∧ G.Adj x a ∧ G.Adj x b ∧
      ∀ w ∈ X, ¬ G.Adj r w → w = x) := by
  classical
  constructor
  · by_contra! neither
    obtain ⟨_,_,_,one⟩ := unique_of_not_two F no P neither.1
    obtain ⟨_,_,_,two⟩ := unique_of_not_two F.swap_first_two no P neither.2
    exact no (F.traceable_of_two_almost_complete P one two)
  · intro h
    obtain ⟨x,xX,off,one⟩ := unique_of_not_two F no P h
    obtain ⟨_,_,xa,xb,degree⟩ := F.unique_miss_degree_and_contacts no P one
    exact ⟨x,xX,off,degree,xa,xb,one⟩

/-- Graph-level statement at the catalogue connectivity and minimum-order
interface. The assertion ranges over every ordering of every separating triple. -/
theorem catalogue_minimum_port_deficiency
    (minimum : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), Fintype.card W < Fintype.card V →
      H.Connected → 2 ≤ Fintype.card W → treeNumber H ≤ vertexConnectivity H + 2 → Traceable H)
    (k : vertexConnectivity G = 3) (bound : treeNumber G ≤ vertexConnectivity G + 2)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ u v, G.degree u = 3 → G.degree v = 3 → ¬ G.Adj u v) :
    (∃ D : Finset V, D.card = 3 ∧ ¬ (DeletionGraph G D).Preconnected) ∧
    ∀ D : Finset V, D.card = 3 → ¬ (DeletionGraph G D).Preconnected →
      ∃ z : V, ∃ X : Set V, ∃ P : PathOn G {v | v ≠ z},
      ∀ r a b : V, r ≠ a → r ≠ b → a ≠ b → D = {r,a,b} →
        SingletonCut G X z r a b ∧ SaturatedPort G X r a b ∧
        (P.terminalQuartet.card = 4 ∧ (∀ v ∈ P.terminalQuartet, v ∈ X) ∧
          (∀ v ∈ P.terminalQuartet, ∀ w ∈ P.terminalQuartet, ¬ G.Adj v w) ∧
          ∀ s ∈ D, ∃ v ∈ P.terminalQuartet, ¬ G.Adj s v) ∧
        (MissesTwo G X r ∨ MissesTwo G X a) ∧
        (¬ MissesTwo G X r → ∃ x ∈ X, ¬ G.Adj r x ∧ G.degree x = 3 ∧ G.Adj x a ∧ G.Adj x b ∧
          ∀ w ∈ X, ¬ G.Adj r w → w = x) := by
  obtain ⟨existsCut,every⟩ := catalogue_minimum_singleton_profile minimum k bound order no ind
  refine ⟨existsCut,?_⟩
  intro D size cut
  obtain ⟨z,X,⟨P⟩,all⟩ := every D size cut
  refine ⟨z,X,P,?_⟩
  intro r a b ra rb ab eq
  obtain ⟨F,sat,_,_⟩ := all r a b ra rb ab eq
  exact ⟨F,sat,⟨by rw [P.terminalQuartet_card no,F.cubic],F.flanks_in_shore no P,
    P.terminalQuartet_independent no,fun s hs => F.misses_flank no P (eq ▸ hs)⟩,
    F.port_pair_profile no P⟩

#print axioms SingletonCut.port_pair_profile
#print axioms catalogue_minimum_port_deficiency
end Graffiti199Depleted.Catalogue.Incomplete
