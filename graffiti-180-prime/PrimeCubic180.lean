import ModuleQuotient180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V)

/-- Minimality under proper connected induced subgraphs of order at least two. -/
def ProperSidesGood : Prop := ∀ S : Finset V,S.card<Fintype.card V → 1<S.card → (side H S).Connected →
  ∀ r p,localBound (side H S) r (parity (side H S) r p)

theorem no_port_of_failure (hc : H.Connected) (hn : 1<Fintype.card V) (r : V) (p : Bool)
    (bad : ¬localBound H r (parity H r p)) (y : V) (edge : H.Adj r y) :
    ∃ z,z≠r ∧ z≠y ∧ ¬H.Adj z r ∧ ¬H.Adj z y := by
  by_contra! miss
  apply bad (dom_edge_rooted H hc hn ⟨edge,?_⟩ p)
  intro x xr xy
  exact or_iff_not_imp_left.mpr (miss x xr xy)

theorem minimal_boundary (hc : H.Connected) (min : ProperSidesGood H) (r : V) (p : Bool)
    (bad : ¬localBound H r (parity H r p)) (M : Finset V) (hom : Homogeneous H M)
    (fat : 1<M.card) (proper : M≠univ) (a : V) (am : a∈M) : 4≤(outside H M a).card := by
  by_contra! small
  obtain ⟨order,lt,gc,fail⟩ := low_module_descent H hc M hom a am fat proper (by omega) r p bad
  rw [Fintype.card_coe] at order lt
  exact fail (min _ lt order gc _ p)

theorem minimal_noCut (hc : H.Connected) (min : ProperSidesGood H) (r : V) (p : Bool)
    (bad : ¬localBound H r (parity H r p)) : NoCut H := by
  by_contra cut
  obtain ⟨c,S,T,s⟩ := split_of_cut cut
  have ok {X Y} (q : Split H c X Y) := min X q.smallL (by simpa only [Fintype.card_coe] using q.largeL) (q.connectedL hc)
  rcases s.either r with h|h
  · exact bad (s.parity_join hc ⟨r,h⟩ p (ok s) (ok s.flip))
  · exact bad (s.flip.parity_join hc ⟨r,h⟩ p (ok s.flip) (ok s))

theorem minimal_subcubic_prime (hc : H.Connected) (low : ∀ v,H.degree v≤3) (min : ProperSidesGood H)
    (r : V) (p : Bool) (bad : ¬localBound H r (parity H r p)) : Prime H := by
  intro M hom fat
  by_contra proper
  obtain ⟨a,am⟩ := card_pos.mp (show 0<M.card by omega)
  have many := minimal_boundary H hc min r p bad M hom fat proper a am
  have cap : (outside H M a).card≤H.degree a := by
    rw [←card_neighborFinset_eq_degree]; exact card_le_card sdiff_subset
  have := low a; omega

omit [DecidableEq V] in
theorem side_degree_le (S : Finset V) (v : ↥S) : (side H S).degree v≤H.degree v.val := by
  classical
  have inc : push ((side H S).neighborFinset v)⊆H.neighborFinset v.val := by
    rintro _ h
    obtain ⟨w,wm,rfl⟩ := mem_map.mp h
    exact (H.mem_neighborFinset _ _).mpr (((side H S).mem_neighborFinset _ _).mp wm)
  simpa only [card_push,card_neighborFinset_eq_degree] using card_le_card inc

/-- It suffices to settle the subcubic rooted problem on prime blocks
whose chosen root has no incident dominating edge. -/
theorem prime_subcubic_reduction
    (base : ∀ {W : Type u} [Fintype W] [DecidableEq W] (J : SimpleGraph W),J.Connected →
      1<Fintype.card W → (∀ v,J.degree v≤3) → Prime J → NoCut J → ∀ r p,
      (∀ y,J.Adj r y → ∃ z,z≠r ∧ z≠y ∧ ¬J.Adj z r ∧ ¬J.Adj z y) → localBound J r (parity J r p))
    (hc : H.Connected) (hn : 1<Fintype.card V) (low : ∀ v,H.degree v≤3) :
    ∀ r p,localBound H r (parity H r p) := by
  classical
  generalize ord : Fintype.card V=n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    intro r p
    by_contra bad
    have min : ProperSidesGood H := by
      intro S smaller order con
      apply ih (Fintype.card ↥S) (by rw [Fintype.card_coe,←ord]; exact smaller) (side H S) con
        (fun v => (side_degree_le H S v).trans (low v.val)) rfl (by simpa only [Fintype.card_coe] using order)
    have hn' : 1<Fintype.card V := by omega
    exact bad (base H hc hn' low (minimal_subcubic_prime H hc low min r p bad) (minimal_noCut H hc min r p bad)
      r p (no_port_of_failure H hc hn' r p bad))

#print axioms no_port_of_failure
#print axioms minimal_boundary
#print axioms minimal_noCut
#print axioms minimal_subcubic_prime
#print axioms prime_subcubic_reduction
end Minimal180.Substitution
