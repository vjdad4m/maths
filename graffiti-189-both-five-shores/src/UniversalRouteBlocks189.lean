import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

/-- Union of a list of disjoint candidate path blocks. -/
def blockCover (L : List (Finset V)) : Finset V :=
  L.foldr (· ∪ ·) ∅

private theorem mem_blockCover {L : List (Finset V)} {w : V} :
    w∈blockCover L ↔ ∃ B∈L,w∈B := by
  induction L with
  | nil => simp [blockCover]
  | cons A L ih =>
    change w∈A∪blockCover L ↔ _
    rw [mem_union,ih]
    constructor
    · rintro (aw|⟨B,bl,wb⟩)
      · exact ⟨A,List.mem_cons_self,aw⟩
      exact ⟨B,List.mem_cons_of_mem _ bl,wb⟩
    rintro ⟨B,bl,wb⟩
    rcases List.mem_cons.mp bl with rfl|bl
    · exact .inl wb
    exact .inr ⟨B,bl,wb⟩

/-- Universal vertices separate all the path blocks. A spare universal
vertex permits a universal terminal in addition to the prescribed root. -/
theorem universal_route_from_blocks
    (L : List (Finset V)) (K : Finset V) {x : V} (xk : x∈K)
    (pair : L.Pairwise Disjoint)
    (apart : Disjoint K (blockCover L))
    (routes : ∀ B∈L,∃ u∈B,∃ v∈B,RouteOn G B u v)
    (join : ∀ u∈K,∀ w∈K∪blockCover L,u≠w → G.Adj u w)
    (enough : L.length≤K.card) :
    ∃ y,RouteOn G (K∪blockCover L) x y ∧ (L.length<K.card → y∈K) := by
  classical
  induction L generalizing K x with
  | nil =>
    have h : CompleteOn G K := fun u uk w wk ne=>join u uk w (mem_union_left _ wk) ne
    obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique K h xk
    refine ⟨y,?_,fun _=>(ps y).mp p.end_mem_support⟩
    simpa [blockCover] using (show RouteOn G K x y from ⟨p,pp,ps⟩)
  | cons A L ih =>
    change Disjoint K (A∪blockCover L) at apart
    have aa := (disjoint_union_right.mp apart).1
    have al := (disjoint_union_right.mp apart).2
    obtain ⟨u,ua,v,va,p⟩ := routes A List.mem_cons_self
    have xx : x∉A := fun h=>disjoint_left.mp aa xk h
    have edge : G.Adj x u :=
      join x xk u (mem_union_right _ (mem_union_left _ ua)) (fun e=>xx (e.symm ▸ ua))
    have part := p.prefix edge xx
    let R := K.erase x
    have size : R.card=K.card-1 := card_erase_of_mem xk
    have lim : L.length≤R.card := by simp only [List.length_cons] at enough; omega
    by_cases n : R.card=0
    · have Lnil : L=[] := List.length_eq_zero_iff.mp (by omega)
      have Rnil : R=∅ := card_eq_zero.mp n
      have ke : K={x} := by
        have e := insert_erase xk
        change insert x R=K at e
        rw [Rnil] at e
        exact e.symm
      refine ⟨v,?_,?_⟩
      · simpa [blockCover, Lnil, ke] using part
      simp only [List.length_cons,List.length_eq_zero_iff.mpr Lnil]
      have k : K.card=1 := by simp [ke]
      omega
    obtain ⟨y,yr⟩ := card_pos.mp (show 0<R.card by omega)
    have ry := (mem_erase.mp yr).2
    have yx := (mem_erase.mp yr).1
    have tail := (List.pairwise_cons.mp pair).2
    have dA : Disjoint A (blockCover L) := by
      apply disjoint_left.mpr
      intro w wa wb
      obtain ⟨B,bl,ww⟩ := mem_blockCover.mp wb
      exact disjoint_left.mp ((List.pairwise_cons.mp pair).1 B bl) wa ww
    have rK : R⊆K := erase_subset _ _
    obtain ⟨z,q,zK⟩ := ih R yr tail (al.mono_left rK)
      (fun B h=>routes B (List.mem_cons_of_mem _ h))
      (fun i ri j jm ne=>join i (rK ri) j (by
        rcases mem_union.mp jm with jR|jL
        · exact mem_union_left _ (rK jR)
        exact mem_union_right _ (mem_union_right _ jL)) ne) lim
    have dd : Disjoint (insert x A) (R∪blockCover L) := by
      apply disjoint_left.mpr
      intro w wm wr
      rcases mem_insert.mp wm with rfl|wa
      · rcases mem_union.mp wr with xr|xl
        · exact (mem_erase.mp xr).1 rfl
        exact disjoint_left.mp al xk xl
      rcases mem_union.mp wr with rr|ll
      · exact disjoint_left.mp aa (rK rr) wa
      exact disjoint_left.mp dA wa ll
    have link : G.Adj v y := (join y ry v (mem_union_right _ (mem_union_left _ va))
      (fun e=>disjoint_left.mp aa ry (e.symm ▸ va))).symm
    have ans := part.join q dd link
    have shape : insert x A ∪ (R∪blockCover L)=K∪blockCover (A::L) := by
      ext w
      by_cases e : w=x
      · subst w
        simp [xk]
      simp [blockCover,R,e,or_assoc,or_left_comm,or_comm]
    refine ⟨z,shape ▸ ans,?_⟩
    intro strict
    simp only [List.length_cons] at strict
    exact rK (zK (by omega))

#print axioms universal_route_from_blocks
end Graffiti189LongestPath.CrossSaturation
