import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace GraphPathLift
open SimpleGraph

variable {V W : Type*}

/-- A Mathlib path that visits every vertex. -/
def HasSpanningPath (G : SimpleGraph V) : Prop :=
  ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v, v ∈ p.support

/-- Precisely the consecutive pairs of this vertex sequence, in list order. -/
def edgePairs : List V → List (V × V)
  | a :: (b :: t) => (a,b) :: edgePairs (b::t)
  | _ => []

@[simp] theorem edgePairs_singleton (a : V) : edgePairs [a] = [] := rfl

theorem walk_of_list (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ edgePairs (a::l), G.Adj e.1 e.2) :
    ∃ b, ∃ p : G.Walk a b, p.support = a::l := by
  induction l generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b t ih =>
    have hab : G.Adj a b := h (a,b) (by simp [edgePairs])
    have ht : ∀ e ∈ edgePairs (b::t), G.Adj e.1 e.2 := by
      intro e he
      exact h e (by simp [edgePairs,he])
    obtain ⟨c,p,hp⟩ := ih b ht
    exact ⟨c,.cons hab p,by simp [hp]⟩

theorem spanningPath_of_list (G : SimpleGraph V) (l : List V) (hn : l ≠ [])
    (hd : l.Nodup) (hc : ∀ v, v ∈ l) (h : ∀ e ∈ edgePairs l, G.Adj e.1 e.2) :
    HasSpanningPath G := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons a t =>
    obtain ⟨b,p,hp⟩ := walk_of_list G a t h
    exact ⟨a,b,p,Walk.IsPath.mk' (hp.symm ▸ hd),hp.symm ▸ hc⟩

theorem hasSpanningPath_map (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) (hf : Function.Bijective f) (h : HasSpanningPath G) :
    HasSpanningPath H := by
  obtain ⟨a,b,p,hp,hmem⟩ := h
  refine ⟨f a,f b,p.map f,(Walk.map_isPath_iff_of_injective hf.injective).mpr hp,?_⟩
  intro w
  obtain ⟨v,rfl⟩ := hf.surjective w
  rw [Walk.support_map]
  exact List.mem_map.mpr ⟨v,hmem v,rfl⟩

theorem hasSpanningPath_iso_iff (G : SimpleGraph V) (H : SimpleGraph W) (f : G ≃g H) :
    HasSpanningPath G ↔ HasSpanningPath H :=
  ⟨hasSpanningPath_map G H f.toHom f.bijective,
   hasSpanningPath_map H G f.symm.toHom f.symm.bijective⟩

end GraphPathLift
