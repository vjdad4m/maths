import CubicPairGeometry
import ShortestConnector

namespace Graffiti199Depleted.CubicEdge

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable {P Q : CubicEdge G}

private theorem not_adjacent_both {z : V} (P : CubicEdge G) (s : Bool) :
    ¬ (G.Adj z (P.low s) ∧ G.Adj z (P.low (!s))) := by
  rintro ⟨a,b⟩
  cases s
  · exact P.no_common z ⟨a,b⟩
  · exact P.no_common z ⟨b,a⟩

/-- An induced matching of two cubic edges needs at least three common
boundary vertices. This uses the shortest-connector theorem after
deleting the common boundary. -/
theorem three_le_common_ports (apart : P.Apart Q)
    (conn : Catalogue.ConnectivityAtLeast G 3) (budget : Catalogue.treeNumber G ≤ 5) :
    3 ≤ (P.commonPorts Q).card := by
  classical
  let R := P.ports ∩ Q.ports
  change 3 ≤ R.card
  by_contra! small
  have privateP : ∃ x ∈ P.ports, x ∉ Q.ports := by
    by_contra! h
    have sub : P.ports ⊆ R := fun v hv => Finset.mem_inter.mpr ⟨hv,h v hv⟩
    have le := Finset.card_le_card sub
    rw [P.ports_card] at le
    omega
  have privateQ : ∃ y ∈ Q.ports, y ∉ P.ports := by
    by_contra! h
    have sub : Q.ports ⊆ R := fun v hv => Finset.mem_inter.mpr ⟨h v hv,hv⟩
    have le := Finset.card_le_card sub
    rw [Q.ports_card] at le
    omega
  obtain ⟨x,xP,xNotQ⟩ := privateP
  obtain ⟨y,yQ,yNotP⟩ := privateQ
  obtain ⟨s,xs,xoff⟩ := P.neighbor_half xP
  obtain ⟨t,yt,yoff⟩ := Q.neighbor_half yQ
  let a := P.low s
  let b := P.low (!s)
  let c := Q.low t
  let e := Q.low (!t)
  have Ppair : G.Adj a b := P.low_adj s
  have Qpair : G.Adj c e := Q.low_adj t
  have xQ := apart.private_port_outside_other_region xP xNotQ
  have yP := apart.symm.private_port_outside_other_region yQ yNotP
  have noPL (i : Bool) : ¬ G.Adj (P.low i) y :=
    fun h => yP (P.low_neighbor_mem_region h)
  have noQL (j : Bool) : ¬ G.Adj x (Q.low j) :=
    fun h => xQ (Q.low_neighbor_mem_region h.symm)
  have path : Catalogue.InducedSixPath G := by
    by_cases xy : G.Adj x y
    · exact Catalogue.inducedSixPath_of_edges Ppair.symm xs.symm xy yt Qpair
        (fun h => xoff h.symm) (noPL (!s)) (apart.no_cross (!s) t) (apart.no_cross (!s) (!t))
        (noPL s) (apart.no_cross s t) (apart.no_cross s (!t)) (noQL t) (noQL (!t)) yoff
    let T := (↑R : Set V)ᶜ
    let H := G.induce T
    have connH : H.Connected := conn.2 R small
    let lift (z : V) (h : z ∉ R) : T := ⟨z,h⟩
    have pKeeps (i : Bool) : P.low i ∉ R :=
      fun h => P.low_not_port i (Finset.mem_inter.mp h).1
    have qKeeps (i : Bool) : Q.low i ∉ R :=
      fun h => Q.low_not_port i (Finset.mem_inter.mp h).2
    let x' := lift x (fun h => xNotQ (Finset.mem_inter.mp h).2)
    let y' := lift y (fun h => yNotP (Finset.mem_inter.mp h).1)
    let a' := lift a (pKeeps s)
    let b' := lift b (pKeeps (!s))
    let c' := lift c (qKeeps t)
    let e' := lift e (qKeeps (!t))
    let A : Set T := {x',a',b'}
    let B : Set T := {y',c',e'}
    have Asub (u : T) (hu : u ∈ A) : u.val ∈ P.region := by
      rcases (show u = x' ∨ u = a' ∨ u = b' by simpa [A] using hu) with rfl|rfl|rfl
      · exact Or.inr xP
      · exact P.low_mem_region s
      · exact P.low_mem_region (!s)
    have Boff (u : T) (hu : u ∈ B) : u.val ∉ P.region := by
      rcases (show u = y' ∨ u = c' ∨ u = e' by simpa [B] using hu) with rfl|rfl|rfl
      · exact yP
      · exact apart.no_low_in_other_region t
      · exact apart.no_low_in_other_region (!t)
    have dis : Disjoint A B := Set.disjoint_left.mpr fun _ hu hv => Boff _ hv (Asub _ hu)
    have anti : ∀ u ∈ A, ∀ v ∈ B, ¬ H.Adj u v := by
      intro u hu v hv
      rcases (show u = x' ∨ u = a' ∨ u = b' by simpa [A] using hu) with rfl|rfl|rfl
      · rcases (show v = y' ∨ v = c' ∨ v = e' by simpa [B] using hv) with rfl|rfl|rfl
        · exact xy
        · exact noQL t
        · exact noQL (!t)
      · exact fun h => Boff _ hv (P.low_neighbor_mem_region (b := s) h)
      · exact fun h => Boff _ hv (P.low_neighbor_mem_region (b := !s) h)
    have outside (z : T) (za : z ∉ A) (zb : z ∉ B) :
        ¬ (H.Adj z a' ∧ H.Adj z b') ∧ ¬ (H.Adj z c' ∧ H.Adj z e') ∧
          ¬ ((H.Adj z a' ∨ H.Adj z b') ∧ (H.Adj z c' ∨ H.Adj z e')) := by
      have offP (i : Bool) : z.val ≠ P.low i := by
        intro eq
        apply za
        have he : z = lift (P.low i) (pKeeps i) := Subtype.ext eq
        cases s <;> cases i <;> simp [A, he, a', b', a, b]
      have offQ (i : Bool) : z.val ≠ Q.low i := by
        intro eq
        apply zb
        have he : z = lift (Q.low i) (qKeeps i) := Subtype.ext eq
        cases t <;> cases i <;> simp [B, he, c', e', c, e]
      have zP (i) (edge : G.Adj z.val (P.low i)) := P.mem_ports.mpr ⟨offP,i,edge⟩
      have zQ (i) (edge : G.Adj z.val (Q.low i)) := Q.mem_ports.mpr ⟨offQ,i,edge⟩
      refine ⟨P.not_adjacent_both s,Q.not_adjacent_both t,?_⟩
      rintro ⟨p,q⟩
      exact z.property (Finset.mem_inter.mpr ⟨p.elim (zP s) (zP (!s)),q.elim (zQ t) (zQ (!t))⟩)
    exact (Catalogue.inducedSixPath_of_anticomplete_paths (G := H) connH
      (x := x') (a := a') (b := b') (y := y') (c := c') (e := e')
      xs Ppair xoff yt Qpair yoff dis anti outside).of_induce
  have six := path.le_treeNumber
  omega

#print axioms three_le_common_ports

end Graffiti199Depleted.CubicEdge
