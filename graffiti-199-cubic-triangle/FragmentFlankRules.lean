import RoutedFragments

open private traceable_of_omission_permutation from OmissionSplice

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (SixTree six_tree_absurd)

def BlocksFirst {n} (b : Layout n) (e : Fin (n+1) → Fin (n+1) → Bool) : Prop :=
  ∃ i, e 0 (b.next i) = true
def BlocksLast {n} (b : Layout n) (e : Fin (n+1) → Fin (n+1) → Bool) : Prop :=
  ∃ i, e (rightEnd n) (b.prev i) = true

instance blocksFirstDecidable {n} (b : Layout n) (e : Fin (n+1) → Fin (n+1) → Bool) :
    Decidable (BlocksFirst b e) := by unfold BlocksFirst; infer_instance
instance blocksLastDecidable {n} (b : Layout n) (e : Fin (n+1) → Fin (n+1) → Bool) :
    Decidable (BlocksLast b e) := by unfold BlocksLast; infer_instance

structure FragmentFlanks (n k : ℕ) (b : Layout n) (e : Fin (n+1) → Fin (n+1) → Bool)
    (D : Seams n k) (mate : Fin (n+1)) where
  profiles : List ℕ
  single : SingleChecks e mate profiles
  lmask : ℕ
  rmask : ℕ
  linked : Bool
  stop : ∃ i, touch lmask (b.next i) = true
  someFlank : BlocksFirst b e ∨ BlocksLast b e
  leftEmpty : ¬ BlocksFirst b e → ∀ m ∈ profiles, touch m (rightEnd n) = true →
    ∃ route : FragmentRoute n k, route.Valid D e ∧ touch m route.last = true
  rightEmpty : ¬ BlocksLast b e → ∀ m ∈ profiles, touch m (0 : Fin (n+1)) = true →
    ∃ route : FragmentRoute n k, route.Valid D e ∧ touch m route.first = true
  pair : ∀ a d t, a ∈ profiles → d ∈ profiles → touch a (0 : Fin (n+1)) = true →
    touch d (rightEnd n) = true →
      (∃ T, SixTree (pairEdge e a d t) T) ∨
      (∃ p : FragmentRoute n k, p.Valid D e ∧ touch a p.first = true ∧ touch d p.last = true) ∨
      (a = lmask ∧ d = rmask ∧ t = linked)
  advance : lmask ∈ profiles → rmask ∈ profiles → ∀ m t,
    m ∈ profiles →
      (∃ T, SixTree (fragmentStepEdge e lmask rmask m linked t) T) ∨
      (∃ p : FragmentRoute n k, p.Valid D e ∧
        ((touch lmask p.first = true ∧ touch rmask p.last = true) ∨
         (touch m p.first = true ∧ touch lmask p.last = true ∧ linked = true))) ∨
      (m = lmask ∧ t = linked)

variable {V : Type*} {G : SimpleGraph V}

theorem trace_of_framed_route [DecidableEq V] {z : V} (p : PathOn G {x | x ≠ z})
    {L B R : List V} (order : (L ++ B ++ R).Perm p.vertices)
    {s t : V} (w : RealizedRoute G s t z B)
    (lc : L.Chain' G.Adj) (rc : R.Chain' G.Adj)
    (left : ∀ x ∈ L.getLast?, G.Adj x s) (right : ∀ y ∈ R.head?, G.Adj t y) :
    Catalogue.Traceable G := by
  have ne : w.vertices ≠ [] := by intro h; have e := w.first; rw [h] at e; cases e
  have tail : (w.vertices ++ R).Chain' G.Adj := by
    apply w.chain.append rc
    intro x hx y hy
    rw [w.last] at hx
    have eq : t = x := by simpa using hx
    exact eq ▸ right y hy
  have chain : (L ++ (w.vertices ++ R)).Chain' G.Adj := by
    apply lc.append tail
    intro x hx y hy
    rw [List.head?_append_of_ne_nil _ ne,w.first] at hy
    have eq : s = y := by simpa using hy
    exact eq ▸ left x hx
  have hperm : (L ++ (w.vertices ++ R)).Perm (z :: p.vertices) := by
    apply ((w.perm.append_right R).append_left L).trans
    simpa only [List.append_assoc,List.cons_append] using
      (List.perm_middle (a := z) (l₁ := L) (l₂ := B ++ R)).trans
        (by simpa only [List.append_assoc] using (order.cons z))
  exact traceable_of_omission_permutation p hperm chain

end Graffiti199Depleted.WiderOmission
