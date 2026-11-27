import NestedCorePrivateCrossLift133
import CambyDomBase133

namespace Graffiti133PrivateCross
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def nextArc (q : Fin 7) (i : Fin 6) : Fin 7 := q+Fin.castLE (by decide) i+1

private theorem next_arc_geometry :
    (∀ q : Fin 7,∀ i : Fin 6,nextArc q i≠q) ∧
    (∀ q j : Fin 7,j≠q→∃ i : Fin 6,nextArc q i=j) ∧
    (∀ q : Fin 7,∀ i j : Fin 6,
      i.val+1=j.val ∨ j.val+1=i.val → Cyclic (nextArc q i) (nextArc q j)) ∧
    (∀ q : Fin 7,Cyclic (nextArc q 0) q) ∧
    (∀ q : Fin 7,Cyclic q (q+1)) := by decide

theorem cycle_two_control_core_connected_after_delete
    (H : Hole G 7) (D : Finset V) (cy : ∀ i,H.c i∈D)
    (u v : V) (shape : ∀ w∈D,(∃ i,H.c i=w) ∨ w=u ∨ w=v)
    (us : ∃ i j : Fin 7,i≠j ∧ G.Adj u (H.c i) ∧ G.Adj u (H.c j))
    (vs : ∃ i j : Fin 7,i≠j ∧ G.Adj v (H.c i) ∧ G.Adj v (H.c j))
    (x : V) : (G.induce (D.erase x : Set V)).Connected := by
  classical
  obtain ⟨q,hq⟩ : ∃ q : Fin 7,∀ j,j≠q→H.c j≠x := by
    by_cases ex : ∃ i,H.c i=x
    · obtain ⟨q,eq⟩ := ex
      exact ⟨q,fun j ne e=>ne (H.inj (e.trans eq.symm))⟩
    · exact ⟨0,fun j _ e=>ex ⟨j,e⟩⟩
  let W := (D.erase x : Set V)
  let J := G.induce W
  let P (i : Fin 6) : W := ⟨H.c (nextArc q i),
    Finset.mem_erase.mpr ⟨hq _ (next_arc_geometry.1 q i),cy _⟩⟩
  have pathReach (k : Nat) (k6 : k<6) : J.Reachable (P 0) (P ⟨k,k6⟩) := by
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      have kk : k<6 := by omega
      have ed : J.Adj (P ⟨k,kk⟩) (P ⟨k+1,k6⟩) :=
        (H.adj _ _).mpr (next_arc_geometry.2.2.1 q ⟨k,kk⟩ ⟨k+1,k6⟩ (Or.inl rfl))
      exact (ih kk).trans ed.reachable
  have step (w y : W) (h : J.Reachable (P 0) w) (e : J.Adj w y) :
      J.Reachable (P 0) y := h.trans e.reachable
  have cReach (j : Fin 7) (m : H.c j∈D.erase x) :
      J.Reachable (P 0) ⟨H.c j,m⟩ := by
    by_cases same : j=q
    · subst j
      exact (show J.Adj (P 0) ⟨H.c q,m⟩ from (H.adj _ _).mpr (next_arc_geometry.2.2.2.1 _)).reachable
    · obtain ⟨i,e⟩ := next_arc_geometry.2.1 q j same
      have r : J.Reachable (P 0) (P i) := pathReach i.val i.isLt
      have eq : P i=⟨H.c j,m⟩ := Subtype.ext (congrArg H.c e)
      exact eq ▸ r
  have gateReach (w : W) (h : ∃ i j : Fin 7,i≠j ∧ G.Adj w.val (H.c i) ∧ G.Adj w.val (H.c j)) :
      J.Reachable (P 0) w := by
    obtain ⟨i,j,ne,ei,ej⟩ := h
    by_cases hi : i=q
    · have hj : j≠q := fun eq=>ne (hi.trans eq.symm)
      have ng := hq j hj
      have m := Finset.mem_erase.mpr ⟨ng,cy j⟩
      exact step _ _ (cReach j m) ej.symm
    · have m := Finset.mem_erase.mpr ⟨hq i hi,cy i⟩
      exact step _ _ (cReach i m) ei.symm
  rw [connected_iff_exists_forall_reachable]
  refine ⟨P 0,?_⟩
  intro w
  rcases shape w.val (Finset.mem_erase.mp w.property).2 with ⟨j,eq⟩|eq|eq
  · have wm : H.c j∈D.erase x := eq.symm ▸ w.property
    have e : (⟨H.c j,wm⟩ : W)=w := Subtype.ext eq
    exact e ▸ cReach j wm
  · exact gateReach w (eq.symm ▸ us)
  · exact gateReach w (eq.symm ▸ vs)

theorem minimum_core_has_canonical_private_witnesses
    (H : Hole G 7) (D : Finset V) (min : MinimalSize G D) (cy : ∀ i,H.c i∈D)
    (u v : V) (uo : Outside H.c u) (vo : Outside H.c v) (uv : u≠v)
    (ud : u∈D) (vd : v∈D) (shape : ∀ w∈D,(∃ i,H.c i=w) ∨ w=u ∨ w=v)
    (us : ∃ i j : Fin 7,i≠j ∧ G.Adj u (H.c i) ∧ G.Adj u (H.c j))
    (vs : ∃ i j : Fin 7,i≠j ∧ G.Adj v (H.c i) ∧ G.Adj v (H.c j)) :
    ∀ a : Fin 9,∃ z,PrivateFor G (canonCore H u v) a z := by
  have inD (a : Fin 9) : canonCore H u v a∈D := by
    fin_cases a <;> simp_all [canonCore]
  have U : Function.Injective (canonCore H u v) := canonCore_injective H u v uo vo uv
  intro a
  let x := canonCore H u v a
  have adj : ∃ y∈D,G.Adj x y := by
    rcases shape x (inD a) with ⟨i,e⟩|e|e
    · exact ⟨H.c (i+1),cy _,e ▸ (H.adj _ _).mpr (next_arc_geometry.2.2.2.2 i)⟩
    · obtain ⟨i,_,_,ai,_⟩ := us
      exact ⟨H.c i,cy i,e.symm ▸ ai⟩
    · obtain ⟨i,_,_,ai,_⟩ := vs
      exact ⟨H.c i,cy i,e.symm ▸ ai⟩
  obtain ⟨y,yd,xy⟩ := adj
  obtain ⟨z,zo,zx,n⟩ := private_of_noncut min (inD a) (Finset.mem_erase.mpr ⟨xy.ne.symm,yd⟩) xy
    (cycle_two_control_core_connected_after_delete H D cy u v shape us vs x)
  refine ⟨z,fun b e=>zo (e.symm ▸ inD b),fun b=>?_⟩
  constructor
  · intro e
    by_contra h
    exact n _ (inD b) (fun e=>h (U e).symm) e
  · rintro rfl
    exact zx

#print axioms cycle_two_control_core_connected_after_delete
#print axioms minimum_core_has_canonical_private_witnesses
end Graffiti133PrivateCross
