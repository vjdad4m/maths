import CubicDiamondCut33

namespace Graffiti384b.CubicShore
open Finset SimpleGraph EarAnchor CliquePivot33 EarExchange33
open private CubicShore.half_tight from CubicDiamondCut33
open private Repair.triangles_le_choose from Repair384b

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem other_score {e a u : V} (one : trianglesAt H e=1) (rare : trianglesAt H a=2 ∨ trianglesAt H a=3)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (ue : u≠e) (ua : u≠a) (du : H.degree u=3) : trianglesAt H u+trianglesAt H a=5 := by
  have not1 : trianglesAt H u≠1 := fun h => ue (inj (h.trans one.symm))
  have diff : trianglesAt H u≠trianglesAt H a := fun h => ua (inj h)
  have cap := Repair.triangles_le_choose H u; rw [du] at cap
  have ub : trianglesAt H u≤3 := cap
  have := pos u; omega

/-- With half-order 2-domination and a low-count endpoint of an ear square, the
remaining three vertices of every five-clique are the entire neighborhood
of the same cubic outside the square. This determines the five-clique. -/
theorem forced_clique {e a c w : V} (de : H.degree e=2) (rare : trianglesAt H a=2 ∨ trianglesAt H a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C) :
    ∃ u,H.degree u=3 ∧ trianglesAt H u+trianglesAt H a=5 ∧ ¬H.Adj u c ∧ ¬H.Adj u w ∧
      (∀ t,H.degree t=3 → t=a ∨ t=u) ∧
      ∀ C,H.IsNClique 5 C → C=insert c (insert w (H.neighborFinset u)) := by
  classical
  have one : trianglesAt H e=1 := by
    have cap := Repair.triangles_le_choose H e
    rw [de,Nat.choose_self] at cap; have := pos e; omega
  have find {C : Finset V} (cl : H.IsNClique 5 C) {x : V} (xm : x∈C\{c,w}) :
      ∃ u,H.degree u=3 ∧ trianglesAt H u+trianglesAt H a=5 ∧ H.Adj u x := by
    obtain ⟨cm,wC⟩ := clique_contains H de rare ea ec aw cw we.symm ac.ne pos inj half cl
    obtain ⟨inC,no⟩ := mem_sdiff.mp xm
    obtain ⟨xc,xw⟩ := (show x≠c ∧ x≠w by simpa [not_or] using no)
    obtain ⟨u,ue,ua,_,du,adj⟩ := blocker H de rare ea ec aw cw we.symm ac.ne pos inj one
      (CubicShore.half_tight H half) cl cm wC inC xc xw
    exact ⟨u,du,other_score H one rare pos inj ue ua du,adj⟩
  have size {C : Finset V} (cl : H.IsNClique 5 C) : (C\{c,w}).card=3 := by
    obtain ⟨cm,wC⟩ := clique_contains H de rare ea ec aw cw we.symm ac.ne pos inj half cl
    rw [card_sdiff (insert_subset cm (singleton_subset_iff.mpr wC)),cl.2,card_pair cw.ne]
  obtain ⟨C,cl⟩ := five
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(C\{c,w}).card by rw [size cl]; decide)
  obtain ⟨u,du,score,_⟩ := find cl xm
  have precise {K : Finset V} (kc : H.IsNClique 5 K) : K\{c,w}=H.neighborFinset u := by
    apply eq_of_subset_of_card_le
    · intro x xk
      obtain ⟨t,_,ts,edge⟩ := find kc xk
      exact (H.mem_neighborFinset _ _).mpr (show H.Adj u x from inj (show trianglesAt H t=trianglesAt H u by omega) ▸ edge)
    · rw [size kc,card_neighborFinset_eq_degree,du]
  have no {t : V} (tm : t∈({c,w} : Finset V)) : ¬H.Adj u t := by
    intro edge; have m := (H.mem_neighborFinset _ _).mpr edge
    rw [← precise cl] at m; exact (mem_sdiff.mp m).2 tm
  refine ⟨u,du,score,no (mem_insert_self ..),no (mem_insert_of_mem (mem_singleton_self _)),?_,?_⟩
  · intro t dt
    by_cases ta : t=a
    · exact Or.inl ta
    have te : t≠e := fun eq => by subst t; omega
    have f := other_score H one rare pos inj te ta dt
    exact Or.inr (inj (by omega))
  · intro K kc
    obtain ⟨cm,wK⟩ := clique_contains H de rare ea ec aw cw we.symm ac.ne pos inj half kc
    rw [← precise kc]
    ext t
    by_cases tc : t=c
    · subst t; simp [cm]
    by_cases tw : t=w
    · subst t; simp [wK]
    simp [tc,tw]

end Graffiti384b.CubicShore
#print axioms Graffiti384b.CubicShore.forced_clique
