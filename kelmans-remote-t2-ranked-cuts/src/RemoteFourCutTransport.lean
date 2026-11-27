import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteFourCutTransport
open SquareCap (boundary SmallTrivial)
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {H : SimpleGraph V} {G : SimpleGraph W} (E : H ≃g G)

omit [DecidableEq V] [DecidableEq W] in
theorem transfer_small (E : H ≃g G) (sm : SmallTrivial G) : SmallTrivial H := by
  classical
  intro c low
  let d : W→Bool := fun x=>c (E.symm x)
  let f : V×V ↪ W×W := ⟨fun p=>(E p.1,E p.2),
    fun p q eq=>Prod.ext (E.injective (congrArg Prod.fst eq)) (E.injective (congrArg Prod.snd eq))⟩
  have identity : (boundary H c).map f=boundary G d := by
    ext ⟨u,v⟩
    constructor
    · intro h
      obtain ⟨⟨a,b⟩,m,eq⟩ := mem_map.mp h
      change (E a,E b)=(u,v) at eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      simp only [boundary,mem_filter,mem_univ,true_and] at m ⊢
      exact ⟨by simpa [d] using m.1,by simpa [d] using m.2.1,E.map_adj_iff.mpr m.2.2⟩
    · intro h
      simp only [boundary,mem_filter,mem_univ,true_and] at h
      refine mem_map.mpr ⟨(E.symm u,E.symm v),?_,?_⟩
      · simp only [boundary,mem_filter,mem_univ,true_and]
        exact ⟨h.1,h.2.1,E.symm.map_adj_iff.mpr h.2.2⟩
      · change (E (E.symm u),E (E.symm v))=(u,v)
        simp
  have card : (boundary G d).card=(boundary H c).card := by rw [←identity,card_map]
  rcases sm d (card.symm ▸ low) with t|f'
  · left
    intro a b aa bb
    apply E.injective
    exact t _ _ (by simpa [d] using aa) (by simpa [d] using bb)
  · right
    intro a b aa bb
    apply E.injective
    exact f' _ _ (by simpa [d] using aa) (by simpa [d] using bb)

variable [DecidableRel H.Adj] [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableEq W] in
theorem transfer_degree (a : V) : H.degree a=G.degree (E a) := by
  classical
  let g : H.neighborSet a ≃ G.neighborSet (E a) :=
    { toFun:=fun v=>⟨E v.val,E.map_adj_iff.mpr v.property⟩
      invFun:=fun v=>⟨E.symm v.val,by
        have h := E.symm.map_adj_iff.mpr v.property
        simpa [E.symm_apply_apply] using h⟩
      left_inv:=fun v=>Subtype.ext (E.symm_apply_apply v.val)
      right_inv:=fun v=>Subtype.ext (E.apply_symm_apply v.val) }
  rw [←H.card_neighborSet_eq_degree,←G.card_neighborSet_eq_degree]
  exact Fintype.card_congr g

#print axioms transfer_small
#print axioms transfer_degree
end KelmansCactus.AtomicBridge.RemoteFourCutTransport
