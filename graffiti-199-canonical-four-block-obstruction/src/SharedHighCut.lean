import ShortestConnector
import PairSeparationAtOrders

open private lowLabel FullPair.low FullPair.low_edge FullPair.low_stays FullPair.low_degree
  FullPair.high_side FullPair.degree_three_off from SharedHighSeparation
open private pair_low_cases from FourBlockIntegration
open private pair_ports_card from PairSeparationAtOrders

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private theorem FullPair.low_in_region (P : FullPair G) (s : Bool) :
    FullPair.low P s ∈ labelRegion P.f := ⟨lowLabel s,rfl⟩

private theorem FullPair.high_in_region (P : FullPair G) {v : V} (h : v ∈ pairPorts P) :
    v ∈ labelRegion P.f := by
  obtain ⟨i,_,hi⟩ := h
  exact ⟨i,hi⟩

private theorem FullPair.not_in_region_of_not_high (P : FullPair G) {v : V}
    (notHigh : v ∉ pairPorts P) (notLow : ∀ s, v ≠ FullPair.low P s) :
    v ∉ labelRegion P.f := by
  rintro ⟨i,hi⟩
  by_cases high : 2 ≤ i.val
  · exact notHigh ⟨i,high,hi⟩
  rcases pair_low_cases i (by omega) with rfl|rfl
  · exact notLow false hi.symm
  · exact notLow true hi.symm

private theorem FullPair.low_neighbor_is_high (P : FullPair G) {v : V}
    (off : ∀ s : Bool, v ≠ FullPair.low P s) (s : Bool) (edge : G.Adj v (FullPair.low P s)) :
    v ∈ pairPorts P := by
  by_contra h
  exact P.not_in_region_of_not_high h off (FullPair.low_stays P s edge.symm)

private theorem FullPair.not_adj_both_lows (P : FullPair G) {z : V}
    (hz : z ∈ pairPorts P) (s : Bool) :
    ¬ (G.Adj z (FullPair.low P s) ∧ G.Adj z (FullPair.low P (!s))) := by
  rintro ⟨ha,hb⟩
  obtain ⟨i,_,no⟩ := FullPair.high_side P hz
  cases s <;> cases i <;> first | exact no ha | exact no hb

variable (F : FourBlockPacking G)

private theorem FourBlockPacking.no_terminal_low_in_depleted
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3) (s : Bool) :
    FullPair.low F.terminal s ∉ labelRegion F.depleted.f := by
  apply FullPair.degree_three_off F.depleted (FullPair.low_degree F.terminal s) _ _ pHigh
  · cases s
    · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 2)
    · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 2)
  · cases s
    · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 3)
    · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 3)

/-- If fewer than three high vertices are shared, deleting them
leaves two induced three-vertex paths. A shortest connection between
them, or a direct edge, forces an induced path on six vertices. -/
theorem FourBlockPacking.three_le_shared_paired_highs
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (conn : Catalogue.ConnectivityAtLeast G 3) (budget : Catalogue.treeNumber G ≤ 5) :
    3 ≤ (verticesIn (pairPorts F.depleted ∩ pairPorts F.terminal)).card := by
  classical
  let P := F.depleted
  let Q := F.terminal
  let R := verticesIn (pairPorts P ∩ pairPorts Q)
  have qHigh (v : V) (hv : v ∈ pairPorts Q) : G.degree v ≠ 3 := F.highDegree v (Or.inr hv)
  change 3 ≤ R.card
  by_contra! small
  have rMem (v : V) : v ∈ R ↔ v ∈ pairPorts P ∧ v ∈ pairPorts Q := mem_verticesIn
  have privateP : ∃ x ∈ pairPorts P, x ∉ pairPorts Q := by
    by_contra! h
    have sub : verticesIn (pairPorts P) ⊆ R := fun v hv =>
      (rMem v).mpr ⟨mem_verticesIn.mp hv,h v (mem_verticesIn.mp hv)⟩
    have le := Finset.card_le_card sub
    rw [pair_ports_card] at le
    omega
  have privateQ : ∃ y ∈ pairPorts Q, y ∉ pairPorts P := by
    by_contra! h
    have sub : verticesIn (pairPorts Q) ⊆ R := fun v hv =>
      (rMem v).mpr ⟨h v (mem_verticesIn.mp hv),mem_verticesIn.mp hv⟩
    have le := Finset.card_le_card sub
    rw [pair_ports_card] at le
    omega
  obtain ⟨x,xP,xNotQ⟩ := privateP
  obtain ⟨y,yQ,yNotP⟩ := privateQ
  obtain ⟨s,xs,xoff⟩ := FullPair.high_side P xP
  obtain ⟨t,yt,yoff⟩ := FullPair.high_side Q yQ
  let a := FullPair.low P s
  let b := FullPair.low P (!s)
  let c := FullPair.low Q t
  let e := FullPair.low Q (!t)
  have Ppair : G.Adj a b := FullPair.low_edge P s
  have Qpair : G.Adj c e := FullPair.low_edge Q t
  have xQ : x ∉ labelRegion Q.f := Q.not_in_region_of_not_high xNotQ
    (fun i eq => pHigh x xP (eq.symm ▸ FullPair.low_degree Q i))
  have yP : y ∉ labelRegion P.f := P.not_in_region_of_not_high yNotP
    (fun i eq => qHigh y yQ (eq.symm ▸ FullPair.low_degree P i))
  have noPL (i : Bool) : ¬ G.Adj (FullPair.low P i) y :=
    fun h => yP (FullPair.low_stays P i h)
  have noQL (j : Bool) : ¬ G.Adj x (FullPair.low Q j) :=
    fun h => xQ (FullPair.low_stays Q j h.symm)
  have noLL (i j : Bool) : ¬ G.Adj (FullPair.low P i) (FullPair.low Q j) :=
    fun h => F.no_terminal_low_in_depleted pHigh j (FullPair.low_stays P i h)
  have path : Catalogue.InducedSixPath G := by
    by_cases xy : G.Adj x y
    · exact Catalogue.inducedSixPath_of_edges Ppair.symm xs.symm xy yt Qpair
        (fun h => xoff h.symm) (noPL (!s)) (noLL (!s) t) (noLL (!s) (!t))
        (noPL s) (noLL s t) (noLL s (!t)) (noQL t) (noQL (!t)) yoff
    let H := G.induce ((↑R : Set V)ᶜ)
    have connH : H.Connected := conn.2 R small
    let lift (v : V) (h : v ∉ R) : ((↑R : Set V)ᶜ : Set V) := ⟨v,h⟩
    have pKeeps (i : Bool) : FullPair.low P i ∉ R :=
      fun h => pHigh _ ((rMem _).mp h).1 (FullPair.low_degree P i)
    have qKeeps (i : Bool) : FullPair.low Q i ∉ R :=
      fun h => qHigh _ ((rMem _).mp h).2 (FullPair.low_degree Q i)
    let x' := lift x (fun h => xNotQ ((rMem _).mp h).2)
    let y' := lift y (fun h => yNotP ((rMem _).mp h).1)
    let a' := lift a (pKeeps s)
    let b' := lift b (pKeeps (!s))
    let c' := lift c (qKeeps t)
    let e' := lift e (qKeeps (!t))
    let A : Set ((↑R : Set V)ᶜ : Set V) := {x',a',b'}
    let B : Set ((↑R : Set V)ᶜ : Set V) := {y',c',e'}
    have Asub (u : ((↑R : Set V)ᶜ : Set V)) (hu : u ∈ A) : u.val ∈ labelRegion P.f := by
      rcases (show u = x' ∨ u = a' ∨ u = b' by simpa [A] using hu) with rfl|rfl|rfl
      · exact P.high_in_region xP
      · exact P.low_in_region s
      · exact P.low_in_region (!s)
    have Boff (u : ((↑R : Set V)ᶜ : Set V)) (hu : u ∈ B) : u.val ∉ labelRegion P.f := by
      rcases (show u = y' ∨ u = c' ∨ u = e' by simpa [B] using hu) with rfl|rfl|rfl
      · exact yP
      · exact F.no_terminal_low_in_depleted pHigh t
      · exact F.no_terminal_low_in_depleted pHigh (!t)
    have dis : Disjoint A B := Set.disjoint_left.mpr fun _ hu hv => Boff _ hv (Asub _ hu)
    have anti : ∀ u ∈ A, ∀ v ∈ B, ¬ H.Adj u v := by
      intro u hu v hv
      rcases (show u = x' ∨ u = a' ∨ u = b' by simpa [A] using hu) with rfl|rfl|rfl
      · rcases (show v = y' ∨ v = c' ∨ v = e' by simpa [B] using hv) with rfl|rfl|rfl
        · exact xy
        · exact noQL t
        · exact noQL (!t)
      · exact fun h => Boff _ hv (FullPair.low_stays P s h)
      · exact fun h => Boff _ hv (FullPair.low_stays P (!s) h)
    have outside (z : ((↑R : Set V)ᶜ : Set V)) (za : z ∉ A) (zb : z ∉ B) :
        ¬ (H.Adj z a' ∧ H.Adj z b') ∧ ¬ (H.Adj z c' ∧ H.Adj z e') ∧
          ¬ ((H.Adj z a' ∨ H.Adj z b') ∧ (H.Adj z c' ∨ H.Adj z e')) := by
      have offP (i : Bool) : z.val ≠ FullPair.low P i := by
        intro eq
        apply za
        have he : z = lift (FullPair.low P i) (pKeeps i) := Subtype.ext eq
        cases s <;> cases i <;> simp [A, he, a', b', a, b]
      have offQ (i : Bool) : z.val ≠ FullPair.low Q i := by
        intro eq
        apply zb
        have he : z = lift (FullPair.low Q i) (qKeeps i) := Subtype.ext eq
        cases t <;> cases i <;> simp [B, he, c', e', c, e]
      have zP := P.low_neighbor_is_high offP
      have zQ := Q.low_neighbor_is_high offQ
      refine ⟨?_,?_,?_⟩
      · rintro ⟨ha,hb⟩
        exact P.not_adj_both_lows (zP s ha) s ⟨ha,hb⟩
      · rintro ⟨ha,hb⟩
        exact Q.not_adj_both_lows (zQ t ha) t ⟨ha,hb⟩
      · rintro ⟨p,q⟩
        exact z.property ((rMem _).mpr ⟨p.elim (zP s) (zP (!s)),q.elim (zQ t) (zQ (!t))⟩)
    exact (Catalogue.inducedSixPath_of_anticomplete_paths (G := H) connH
      (x := x') (a := a') (b := b') (y := y') (c := c') (e := e')
      xs Ppair xoff yt Qpair yoff dis anti outside).of_induce
  have six := path.le_treeNumber
  omega

#print axioms FourBlockPacking.three_le_shared_paired_highs

end Graffiti199Depleted
