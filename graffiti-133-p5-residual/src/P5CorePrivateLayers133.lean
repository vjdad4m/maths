import P5DominatingCycleGeometry133
import CambyDomBase133

namespace Graffiti133P5CoreShape
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133P5Radius
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2900000
set_option maxRecDepth 100000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem all_four_arc_except :
    (∀ i : Fin 5,∀ j : Fin 4,siteArc (i+1) j≠i) ∧
    (∀ i j : Fin 5,j≠i → ∃ k : Fin 4,siteArc (i+1) k=j) := by decide

private theorem connected_cycle_erase_site (H : Hole G 5) (E : Finset V)
    (cycle : ∀ i,H.c i∈E) (spans : ∀ x∈E,∃ i,H.c i=x) (i : Fin 5) :
    (G.induce (E.erase (H.c i) : Set V)).Connected := by
  let J := G.induce (E.erase (H.c i) : Set V)
  let a (j : Fin 4) : (E.erase (H.c i) : Set V) :=
    ⟨H.c (siteArc (i+1) j),Finset.mem_erase.mpr
      ⟨fun e=>all_four_arc_except.1 i j (H.inj e),cycle _⟩⟩
  have reach (n : Nat) (nl : n<4) : J.Reachable (a 0) (a ⟨n,nl⟩) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl (a 0)
    | succ n ih =>
      have hn : n<4 := by omega
      have e : J.Adj (a ⟨n,hn⟩) (a ⟨n+1,nl⟩) :=
        (H.adj _ _).mpr ((arc_geometry (i+1)).2.2 _ _ (by exact Nat.lt_succ_self _) |>.mpr rfl)
      exact (ih hn).trans e.reachable
  rw [connected_iff_exists_forall_reachable]
  refine ⟨a 0,fun x=>?_⟩
  obtain ⟨j,e⟩ := spans x.val (Finset.mem_erase.mp x.property).2
  have neq : j≠i := fun h=>(Finset.mem_erase.mp x.property).1 (e.symm.trans (congrArg H.c h))
  obtain ⟨k,hk⟩ := all_four_arc_except.2 i j neq
  have eq : a k=x := Subtype.ext ((congrArg H.c hk).trans e)
  exact eq ▸ reach k.val k.isLt

theorem connected_dominating_C5_erase_outside
    (H : Hole G 5) (D : Finset V) (cy : ∀ i,H.c i∈D)
    (dom : ∀ x∈D,Outside H.c x→∃ i,G.Adj x (H.c i))
    (x : V) (xo : Outside H.c x) :
    (G.induce (D.erase x : Set V)).Connected := by
  let J := G.induce (D.erase x : Set V)
  let a (i : Fin 5) : (D.erase x : Set V) :=
    ⟨H.c i,Finset.mem_erase.mpr ⟨(xo i).symm,cy i⟩⟩
  have reach (n : Nat) (nl : n<5) : J.Reachable (a 0) (a ⟨n,nl⟩) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl (a 0)
    | succ n ih =>
      have hn : n<5 := by omega
      have ring : ∀ i j : Fin 5,i.val+1=j.val → Cyclic i j := by decide
      have e : J.Adj (a ⟨n,hn⟩) (a ⟨n+1,nl⟩) :=
        (H.adj _ _).mpr (ring _ _ rfl)
      exact (ih hn).trans e.reachable
  rw [connected_iff_exists_forall_reachable]
  refine ⟨a 0,fun y=>?_⟩
  by_cases yo : Outside H.c y.val
  · obtain ⟨i,e⟩ := dom y.val (Finset.mem_erase.mp y.property).2 yo
    exact (reach i.val i.isLt).trans (show J.Adj (a i) y from e.symm).reachable
  · unfold Outside at yo
    push_neg at yo
    obtain ⟨i,e⟩ := yo
    have eq : a i=y := Subtype.ext e.symm
    exact eq ▸ reach i.val i.isLt

theorem C5_two_layers_private
    (D : Finset V) (dm : MinimalSize G D)
    (H : Hole (G.induce (D : Set V)) 5)
    (E : Finset (D : Set V)) (em : MinimalSize (G.induce (D : Set V)) E)
    (cy : ∀ i,H.c i∈E) (spans : ∀ x∈E,∃ i,H.c i=x) :
    ∀ i : Fin 5,∃ p : (D : Set V),∃ q : V,
      PrivateAt (G.induce (D : Set V)) E (H.c i) p ∧
      PrivateAt G D p.val q := by
  classical
  let J := G.induce (D : Set V)
  let B : Hole G 5 := ⟨Subtype.val ∘ H.c,Subtype.val_injective.comp H.inj,H.adj⟩
  have cyD (i : Fin 5) : B.c i∈D := (H.c i).property
  have ddom (x : V) (xd : x∈D) (xo : Outside B.c x) : ∃ i,G.Adj x (B.c i) := by
    let X : (D : Set V) := ⟨x,xd⟩
    rcases em.1.2 X with e|⟨z,ze,az⟩
    · obtain ⟨i,hi⟩ := spans X e
      exact (xo i (congrArg Subtype.val hi.symm)).elim
    · obtain ⟨i,hi⟩ := spans z ze
      exact ⟨i,show J.Adj X (H.c i) from hi.symm ▸ az⟩
  intro i
  have cic : ∀ i : Fin 5,Cyclic i (i+1) := by decide
  have e : J.Adj (H.c i) (H.c (i+1)) := (H.adj _ _).mpr (cic i)
  obtain ⟨p,pp⟩ := private_of_noncut em (cy i)
    (Finset.mem_erase.mpr ⟨e.ne.symm,cy (i+1)⟩) e (connected_cycle_erase_site H E cy spans i)
  have px : Outside B.c p.val := by
    intro j eq
    exact pp.1 ((Subtype.ext eq).symm ▸ cy j)
  have edge : G.Adj p.val (B.c i) := pp.2.1
  obtain ⟨q,qp⟩ := private_of_noncut dm p.property
    (Finset.mem_erase.mpr ⟨edge.ne.symm,cyD i⟩) edge
    (connected_dominating_C5_erase_outside B D cyD ddom p.val px)
  exact ⟨p,q,pp,qp⟩

#print axioms connected_dominating_C5_erase_outside
#print axioms C5_two_layers_private
end Graffiti133P5CoreShape
