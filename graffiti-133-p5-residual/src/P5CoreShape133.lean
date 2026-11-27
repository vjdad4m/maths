import P5DominatingCycleGeometry133
import CambyCycleDecomp133

namespace Graffiti133P5CoreShape
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133P5Radius
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem first_arc_tag_gives_p5 (H : Hole G 5) (x : V) (out : Outside H.c x)
    (t : Fin 5) (prof : ∀ k : Fin 4,G.Adj x (H.c (siteArc t k))↔k=0) : ∃ p : Fin 5→V,InducedPath G p := by
  let f (a : Fin 5) := if h : a.val=0 then x else H.c (siteArc t ⟨a.val-1,by have := a.isLt; omega⟩)
  refine ⟨f,?_,?_⟩
  · dsimp only [f]
    intro a b eq
    by_cases az : a.val=0 <;> by_cases bz : b.val=0
    · exact Fin.ext (az.trans bz.symm)
    · simp only [dif_pos az,dif_neg bz] at eq
      exact (out _ eq).elim
    · simp only [dif_neg az,dif_pos bz] at eq
      exact (out _ eq.symm).elim
    · simp only [dif_neg az,dif_neg bz] at eq
      have h : a.val-1=b.val-1 := congrArg (fun i : Fin 4=>i.val) ((arc_geometry t).1 (H.inj eq))
      exact Fin.ext (by omega)
  dsimp only [f]
  intro a b ab
  have lt : a.val<b.val := ab
  have bz : b.val≠0 := by omega
  by_cases az : a.val=0
  · rw [dif_pos az,dif_neg bz,prof]
    constructor
    · intro h
      have hh := congrArg (fun i : Fin 4=>i.val) h
      change b.val-1=0 at hh
      omega
    · intro h
      apply Fin.ext
      change b.val-1=0
      omega
  · rw [dif_neg az,dif_neg bz,H.adj]
    exact ((arc_geometry t).2.2 _ _ (by change a.val-1<b.val-1; omega)).trans
      ⟨fun q=>by change a.val-1+1=b.val-1 at q; omega,
       fun q=>by change a.val-1+1=b.val-1; omega⟩


private theorem adjacent_pair_on_rotated_arc :
    ∀ (i : Fin 5) (k : Fin 4),siteArc (i+1) k∈({i,i+1} : Finset (Fin 5)) ↔ k=0 := by decide

theorem dominating_C5_spans_of_P5free (H : Hole G 5) (h4 : FourCycleFree G) (h5 : NoPath G 5)
    (dom : ∀ x,Outside H.c x→∃ i,G.Adj x (H.c i)) : Function.Surjective H.c := by
  intro x
  by_contra! hc
  have out : Outside H.c x := fun i e=>hc i e.symm
  obtain ⟨i,hit⟩ := dom x out
  rcases allowed_tag_form _ ⟨i,(mem_tags H x i).mpr hit⟩ (tags_allowed H h4 x out) with
    ⟨t,tag⟩|⟨t,tag⟩
  · exact h5 (singleton_tag_gives_p5 H x out t tag)
  · apply h5 (first_arc_tag_gives_p5 H x out (t+1) ?_)
    intro k
    rw [←mem_tags,tag,adjacent_pair_on_rotated_arc]

theorem p3free_walk_complete {W : Type*} {J : SimpleGraph W} (h3 : NoPath J 3)
    {a b : W} (p : J.Walk a b) : a=b ∨ J.Adj a b := by
  classical
  induction p with
  | nil => exact Or.inl rfl
  | @cons x y z xy p ih =>
    rcases ih with rfl|ed
    · exact Or.inr xy
    · by_cases e : x=z
      · exact Or.inl e
      · by_cases xz : J.Adj x z
        · exact Or.inr xz
        · exfalso
          apply h3
          let f : Fin 3→W := ![x,y,z]
          refine ⟨f,?_,?_⟩
          · intro a b h
            fin_cases a <;> fin_cases b <;> simp [f,xy.ne,xy.ne.symm,ed.ne,ed.ne.symm,e,(Ne.symm e)] at h ⊢
          · intro a b lt
            fin_cases a <;> fin_cases b <;> simp [f,xy,ed,xz] at lt ⊢


theorem p5free_C4free_clique_or_spanning_C5 (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : NoPath G 5) : (∃ D : Finset V,CD G D ∧ G.IsClique (D : Set V)) ∨
      ∃ H : Hole G 5,Function.Surjective H.c := by
  rcases connected_domination_decomposition G hc 3 (by decide) h5 with
    ⟨D,cd,h3⟩|⟨H,dom⟩
  · let J := G.induce (D : Set V)
    have no : NoPath J 3 := by
      rintro ⟨p,hp⟩
      exact h3 ⟨Subtype.val ∘ p,⟨Subtype.val_injective.comp hp.1,hp.2⟩,fun i=>(p i).property⟩
    refine Or.inl ⟨D,cd,?_⟩
    intro a ha b hb ab
    obtain ⟨r⟩ := cd.1 ⟨a,ha⟩ ⟨b,hb⟩
    rcases p3free_walk_complete no r with eq|ed
    · exact (ab (congrArg Subtype.val eq)).elim
    · exact ed
  · exact Or.inr ⟨H,dominating_C5_spans_of_P5free H h4 h5 dom⟩

#print axioms dominating_C5_spans_of_P5free
#print axioms p5free_C4free_clique_or_spanning_C5
end Graffiti133P5CoreShape
