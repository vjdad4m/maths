import NestedCorePrivateExpandedFit133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133ExpandedPrivate
variable {V : Type*} {G : SimpleGraph V}
theorem nested_fit_sorted {n : Nat} {f : Fin n→V} (spec : Fin n→Fin n→Option Bool)
    (sym : ∀ a b,spec a b=spec b a)
    (prove : ∀ a b t,a.val≤b.val → spec a b=some t → (G.Adj (f a) (f b)↔t=true)) :
    Fit G f spec := by
  intro a b t h
  by_cases ab : a.val≤b.val
  · exact prove a b t ab h
  · have ba : b.val≤a.val := by omega
    rw [sym] at h
    exact (G.adj_comm _ _).trans (prove b a t ba h)

theorem nested_base_fragment_sound {m : Bool} {f : Fin 18→V} (core : CoreKnown G m f)
    {x y : Nat} {hy : y<18} {xy : x≤y} {t : Bool}
    (cert : baseFragment m x y hy xy=some t) :
    G.Adj (f ⟨x,lt_of_le_of_lt xy hy⟩) (f ⟨y,hy⟩)↔t=true := by
  unfold baseFragment at cert
  by_cases x9 : x<9
  · rw [if_pos x9,Option.some.injEq] at cert
    rw [←cert]
    exact core _ _ (Or.inl x9)
  · rw [if_neg x9] at cert
    contradiction


end Graffiti133NestedWeightedCore
