import RemoteRankUnion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace KelmansCactus.AtomicBridge.RemoteBudgetComponent
open SimpleGraph Finset
open scoped BigOperators
open RemoteRankUnion (Marking)
variable {V I : Type*} {G : SimpleGraph V}

structure Mate (G : SimpleGraph V) where
  mate : V→V
  inv : Function.Involutive mate
  edge : ∀ v,G.Adj v (mate v)

theorem Mate.reverse {q : Mate G} {a b : V} (h : q.mate a=b) : q.mate b=a := by
  rw [←h,q.inv]

def exchangeGraph (p q : Mate G) : SimpleGraph V where
  Adj x y := p.mate x=y ∨ q.mate x=y
  symm := fun _ _ h=>h.elim (fun w=>Or.inl (Mate.reverse w)) (fun w=>Or.inr (Mate.reverse w))
  loopless := by
    intro x e
    rcases e with h|h
    · exact G.loopless x (by simpa only [h] using p.edge x)
    · exact G.loopless x (by simpa only [h] using q.edge x)

theorem different_closed (p q : Mate G) {x y : V}
    (different : p.mate x≠q.mate x)
    (step : (exchangeGraph p q).Adj x y) : p.mate y≠q.mate y := by
  intro same
  rcases step with ep|eq
  · exact different (ep.trans (Mate.reverse (q:=q) (same.symm.trans (Mate.reverse (q:=p) ep))).symm)
  · exact different ((Mate.reverse (q:=p) (same.trans (Mate.reverse (q:=q) eq))).trans eq.symm)

theorem different_reaches (p q : Mate G) {x y : V}
    (different : p.mate x≠q.mate x)
    (reach : (exchangeGraph p q).Reachable x y) :
    p.mate y≠q.mate y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at reach
  induction reach with
  | refl => exact different
  | tail _ e ih => exact different_closed p q ih e

/-- Use the second matching on the entire exchange component of the anchor,
and the first elsewhere. Both matchings preserve this component. -/
noncomputable def splice (p q : Mate G) (a : V) : Mate G := by
  classical
  let H := exchangeGraph p q
  let m := fun x => if H.Reachable a x then q.mate x else p.mate x
  refine ⟨m,?_,?_⟩
  · intro x
    have ep : H.Adj x (p.mate x) := Or.inl rfl
    have eq : H.Adj x (q.mate x) := Or.inr rfl
    by_cases part : H.Reachable a x
    · have partQ := part.trans eq.reachable
      simpa only [m, if_pos part, if_pos partQ] using q.inv x
    · have partP : ¬H.Reachable a (p.mate x) := fun h=>part (h.trans ep.symm.reachable)
      simpa only [m, if_neg part, if_neg partP] using p.inv x
  · intro x
    by_cases part : H.Reachable a x
    · simpa only [m,if_pos part] using q.edge x
    · simpa only [m,if_neg part] using p.edge x

theorem splice_in (p q : Mate G) {a x : V}
    (part : (exchangeGraph p q).Reachable a x) :
    (splice p q a).mate x=q.mate x := by
  classical
  simp [splice,part]

theorem splice_out (p q : Mate G) {a x : V}
    (part : ¬(exchangeGraph p q).Reachable a x) :
    (splice p q a).mate x=p.mate x := by
  classical
  simp [splice,part]

theorem exchange_comm_reach (p q : Mate G) {a x : V} :
    (exchangeGraph p q).Reachable a x ↔ (exchangeGraph q p).Reachable a x := by
  constructor
  · exact fun r=>r.mono (fun _ _ e=>Or.symm e)
  · exact fun r=>r.mono (fun _ _ e=>Or.symm e)

def IsSingleExchange (p q : Mate G) (a : V) : Prop :=
  p.mate a≠q.mate a ∧
  ∀ x,(exchangeGraph p q).Reachable a x ↔ p.mate x≠q.mate x

theorem splice_is_single (p q : Mate G) {a : V} (different : p.mate a≠q.mate a) :
    IsSingleExchange p (splice p q a) a := by
  classical
  let H := exchangeGraph p q
  let r := splice p q a
  have sub : exchangeGraph p r ≤ H := by
    intro x y e
    rcases e with e|e
    · exact Or.inl e
    by_cases area : H.Reachable a x
    · exact Or.inr ((splice_in p q area).symm.trans e)
    · exact Or.inl ((splice_out p q area).symm.trans e)
  have grow {x : V} (p0 : H.Reachable a x) : (exchangeGraph p r).Reachable a x := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at p0
    induction p0 with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail y z p1 e ih =>
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      rcases e with e|e
      · exact Or.inl e
      · exact Or.inr ((splice_in p q
          ((SimpleGraph.reachable_iff_reflTransGen (G:=H) _ _).mpr p1)).trans e)
  refine ⟨fun h=>different (h.trans (splice_in p q (SimpleGraph.Reachable.refl _))),?_⟩
  intro x
  constructor
  · intro hx eq
    have active := different_reaches p q different (hx.mono sub)
    exact active (eq.trans (splice_in p q (hx.mono sub)))
  · intro hx
    by_cases area : H.Reachable a x
    · exact grow area
    · exact (hx (splice_out p q area).symm).elim

noncomputable def cost [Fintype I] (M : Marking G I) (p : Mate G) : Nat := by
  classical
  exact ∑ i : I, if p.mate (M.a i)=M.b i then 1 else 0

theorem cost_splice_conservation [Fintype I] (M : Marking G I) (p q : Mate G) (a : V) :
    cost M (splice p q a)+cost M (splice q p a)=cost M p+cost M q := by
  classical
  unfold cost
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases area : (exchangeGraph p q).Reachable a (M.a i)
  · rw [splice_in p q area,splice_in q p ((exchange_comm_reach p q).mp area),Nat.add_comm]
  · rw [splice_out p q area,splice_out q p (fun h=>area ((exchange_comm_reach p q).mpr h))]

/-- If an admissible rank exposes a chosen edge of a minimum-cost
complementary matching, then already one connected alternating exchange
from that minimum matching exposes it at no greater cost than the target. -/
theorem budget_one_exchange [Fintype I] (M : Marking G I)
    (p q : Mate G) (min : ∀ t,cost M p≤cost M t)
    (a b : V) (old : p.mate a=b) (exposes : q.mate a≠b) :
    ∃ r : Mate G,IsSingleExchange p r a ∧ r.mate a≠b ∧ cost M r≤cost M q := by
  have different : p.mate a≠q.mate a := by
    rw [old]
    exact Ne.symm exposes
  refine ⟨splice p q a,splice_is_single p q different,?_,?_⟩
  · rwa [splice_in p q (SimpleGraph.Reachable.refl _)]
  · have eq := cost_splice_conservation M p q a
    have lower := min (splice q p a)
    omega

/-- The full union, from a minimum-mark rank, is already witnessed by its
unchanged edges and legal single-exchange neighbors; multiple switches are not
needed to expose a cut edge. This is edgewise, not one simultaneous choice. -/
theorem exposed_iff_neighbor [Fintype I] (M : Marking G I) (p : Mate G)
    (min : ∀ t,cost M p≤cost M t) (limit : Nat) (adm : cost M p≤limit) (a b : V) :
    (∃ q : Mate G,cost M q≤limit ∧ q.mate a≠b) ↔
      p.mate a≠b ∨ ∃ q : Mate G,IsSingleExchange p q a ∧ q.mate a≠b ∧ cost M q≤limit := by
  constructor
  · rintro ⟨q,h,n⟩
    by_cases old : p.mate a=b
    · obtain ⟨r,s,ex,co⟩ := budget_one_exchange M p q min a b old n
      exact Or.inr ⟨r,s,ex,le_trans co h⟩
    · exact Or.inl old
  · rintro (n|⟨r,_,ex,co⟩)
    · exact ⟨p,adm,n⟩
    · exact ⟨r,co,ex⟩

#print axioms budget_one_exchange
#print axioms exposed_iff_neighbor
end KelmansCactus.AtomicBridge.RemoteBudgetComponent
