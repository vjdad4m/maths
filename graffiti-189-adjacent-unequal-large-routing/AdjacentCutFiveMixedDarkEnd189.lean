import UniversalRouteSingletons189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
variable {W : Type*} {H : SimpleGraph W} [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false

/-- Enough universal high vertices can absorb singleton high remnants and one
exception, provided it can be placed at the end or between two high remnants. -/
theorem universal_route_with_one_dark_exception
    (K R : Finset W) (apart : Disjoint K R)
    (univK : ∀ u∈K,∀ v∈K∪R,u≠v → H.Adj u v)
    (room : R.card+1≤K.card) (twoK : 2≤K.card)
    {l : W} (lk : l∉K) (lr : l∉R)
    (edges : (∃ v∈K,H.Adj v l) ∨ ∃ p∈R,∃ q∈R,p≠q ∧ H.Adj p l ∧ H.Adj l q) :
    ∃ x∈K,∃ z,RouteOn H (insert l (K∪R)) x z := by
  classical
  rcases edges with ⟨v,vk,vl⟩|⟨p,pr,q,qr,pq,pl,lq⟩
  · have ne : (K.erase v).Nonempty := card_pos.mp (by
      rw [card_erase_of_mem vk]
      omega)
    obtain ⟨x,xm⟩ := ne
    have xa := (mem_erase.mp xm).2
    let K' := K.erase v
    have apart' : Disjoint K' R := apart.mono_left (erase_subset _ _)
    have join : ∀ u∈K',∀ w∈K'∪R,u≠w → H.Adj u w :=
      fun u um w wm uw=>univK u (erase_subset _ _ um) w
        (union_subset_union (erase_subset _ _) (Subset.rfl) wm) uw
    have fit : R.card≤K'.card := by
      rw [show K'.card=K.card-1 from card_erase_of_mem vk]
      omega
    obtain ⟨t,route,_⟩ := universal_route_from_singletons K' R xm apart' join fit
    have tm : t∈K'∪R := by
      obtain ⟨q,_,qs⟩ := route
      exact (qs t).mp q.end_mem_support
    have vOff : v∉K'∪R := by
      intro vm
      rcases mem_union.mp vm with vm|vm
      · exact (mem_erase.mp vm).1 rfl
      · exact disjoint_left.mp apart vk vm
    have vt := univK v vk t (union_subset_union (erase_subset _ _) (Subset.rfl) tm)
      (fun e=>vOff (e.symm ▸ tm))
    have f : insert v (K'∪R)=K∪R := by
      rw [←insert_union,insert_erase vk]
    have rt : RouteOn H (K∪R) x v := f ▸ route.suffix vt.symm vOff
    exact ⟨x,xa,l,rt.suffix vl (by simp [lk,lr])⟩
  · have k : K.Nonempty := card_pos.mp (by omega)
    obtain ⟨x,xm⟩ := k
    let R' := R.erase p |>.erase q
    have sub : R'⊆R := (erase_subset _ _).trans (erase_subset _ _)
    have apart' : Disjoint K R' := apart.mono_right sub
    have join : ∀ u∈K,∀ w∈K∪R',u≠w → H.Adj u w :=
      fun u um w wm uw=>univK u um w (union_subset_union (Subset.rfl) sub wm) uw
    have fit : R'.card<K.card := lt_of_le_of_lt (card_le_card sub) (by omega)
    obtain ⟨t,route,tK⟩ := universal_route_from_singletons K R' xm apart' join fit.le
    have tk := tK fit
    have tp := univK t tk p (mem_union_right _ pr)
      (fun e=>disjoint_left.mp apart (e ▸ tk) pr)
    have block : RouteOn H {p,l,q} p q := RouteOn.three pl lq pq
    have sep : Disjoint (K∪R') ({p,l,q}:Finset W) := by
      apply disjoint_left.mpr
      intro u uh ub
      simp only [mem_insert,mem_singleton] at ub
      rcases ub with rfl|rfl|rfl <;> rcases mem_union.mp uh with h|h
      · exact disjoint_left.mp apart h pr
      · exact (mem_erase.mp (mem_erase.mp h).2).1 rfl
      · exact lk h
      · exact lr (sub h)
      · exact disjoint_left.mp apart h qr
      · exact (mem_erase.mp h).1 rfl
    have f : (K∪R')∪{p,l,q}=insert l (K∪R) := by
      ext u
      simp only [R',mem_union,mem_insert,mem_singleton,mem_erase]
      by_cases a : u=p
      · simp [a,pr]
      by_cases b : u=l
      · simp [b]
      by_cases c : u=q
      · simp [c,qr]
      simp [a,b,c]
    exact ⟨x,xm,q,f ▸ route.join block sep tp⟩

#print axioms universal_route_with_one_dark_exception
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
