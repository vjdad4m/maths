import P5DominatingCycleGeometry133
import CambyCycleDecomp133

namespace Graffiti133P5Radius
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000

def CloseTwo {V : Type*} (G : SimpleGraph V) (x y : V) : Prop :=
  x=y ∨ G.Adj x y ∨ ∃ z,G.Adj x z ∧ G.Adj z y

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem compact_C5 :
    ∀ i j : Fin 5,i=j ∨ Cyclic i j ∨ ∃ z : Fin 5,Cyclic i z ∧ Cyclic z j := by decide

private theorem other_pairs_near :
    (∀ i : Fin 5,({i,i+1} : Finset (Fin 5)) ≠ {3,4} →
      ∃ j∈({i,i+1} : Finset (Fin 5)),j=1 ∨ Cyclic 1 j) ∧
    (∀ i : Fin 5,({i,i+1} : Finset (Fin 5)) ≠ {0,1} →
      ∃ j∈({i,i+1} : Finset (Fin 5)),j=3 ∨ Cyclic 3 j) := by decide

theorem center_dominating_C5 (H : Hole G 5) (h4 : FourCycleFree G) (h5 : NoPath G 5)
    (dom : ∀ x,Outside H.c x→∃ i,G.Adj x (H.c i)) :
    ∃ c : V,∀ x,CloseTwo G c x := by
  have adjForm (x : V) (off : Outside H.c x) :
      ∃ i : Fin 5,tags H x={i,i+1} := by
    obtain ⟨i,hi⟩ := dom x off
    rcases allowed_tag_form _ ⟨i,(mem_tags H x i).mpr hi⟩ (tags_allowed H h4 x off) with
      ⟨j,hj⟩|next
    · exact (h5 (singleton_tag_gives_p5 H x off j hj)).elim
    · exact next
  have central (c : Fin 5) (near : ∀ x,Outside H.c x →
      ∃ j∈tags H x,j=c ∨ Cyclic c j) : ∀ x,CloseTwo G (H.c c) x := by
    intro x
    by_cases off : Outside H.c x
    · obtain ⟨j,jm,h|h⟩ := near x off
      · subst j
        exact Or.inr (Or.inl ((mem_tags H x c).mp jm).symm)
      · exact Or.inr (Or.inr ⟨H.c j,(H.adj _ _).mpr h,((mem_tags H x j).mp jm).symm⟩)
    · unfold Outside at off
      push_neg at off
      obtain ⟨j,hj⟩ := off
      subst x
      rcases compact_C5 c j with eq|ed|⟨t,ct,tj⟩
      · exact Or.inl (congrArg H.c eq)
      · exact Or.inr (Or.inl ((H.adj _ _).mpr ed))
      · exact Or.inr (Or.inr ⟨H.c t,(H.adj _ _).mpr ct,(H.adj _ _).mpr tj⟩)
  by_cases haveA : ∃ y,Outside H.c y ∧ tags H y={0,1}
  · obtain ⟨y,yo,yp⟩ := haveA
    refine ⟨H.c 1,central 1 (fun x xo=>?_ )⟩
    obtain ⟨i,pr⟩ := adjForm x xo
    rw [pr]
    apply other_pairs_near.1 i
    intro e
    exact h5 (opposed_pairs_force_p5 H h4 y x yo xo yp (pr.trans e))
  · refine ⟨H.c 3,central 3 (fun x xo=>?_ )⟩
    obtain ⟨i,pr⟩ := adjForm x xo
    rw [pr]
    apply other_pairs_near.2 i
    intro e
    exact haveA ⟨x,xo,pr.trans e⟩

private theorem p3free_walk_complete {W : Type*} {J : SimpleGraph W} (h3 : NoPath J 3)
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

theorem p5free_has_two_step_center (hc : G.Connected) (h4 : FourCycleFree G) (h5 : NoPath G 5) :
    ∃ c : V,∀ x,CloseTwo G c x := by
  classical
  rcases connected_domination_decomposition G hc 3 (by decide) h5 with ⟨D,dm,dp⟩|⟨H,dom⟩
  · let J := G.induce (D : Set V)
    have h3 : NoPath J 3 := by
      rintro ⟨p,h⟩
      exact dp ⟨Subtype.val ∘ p,⟨Subtype.val_injective.comp h.1,h.2⟩,fun a=>(p a).property⟩
    obtain ⟨q⟩ := dm.1.nonempty
    have top (x : V) (hx : x∈D) : q.val=x ∨ G.Adj q.val x := by
      obtain ⟨p⟩ := dm.1 q ⟨x,hx⟩
      exact (p3free_walk_complete h3 p).imp (congrArg Subtype.val) id
    refine ⟨q.val,fun x=>?_⟩
    rcases dm.2 x with xc|⟨v,vd,xv⟩
    · exact (top x xc).imp id Or.inl
    · rcases top v vd with eq|ad
      · exact Or.inr (Or.inl (eq.symm ▸ xv.symm))
      · exact Or.inr (Or.inr ⟨v,ad,xv.symm⟩)
  · exact center_dominating_C5 H h4 h5 dom

#print axioms center_dominating_C5
#print axioms p5free_has_two_step_center
end Graffiti133P5Radius
