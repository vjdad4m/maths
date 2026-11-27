import OmissionSplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}

namespace PathOn

variable (p : PathOn G {v | v ≠ z})

abbrev EdgePosition := Fin (p.vertices.length - 1)

def before {U : Set V} (p : PathOn G U) (i : Fin (p.vertices.length - 1)) : V :=
  p.vertices[i.val]'(by have := i.isLt; omega)

def after {U : Set V} (p : PathOn G U) (i : Fin (p.vertices.length - 1)) : V :=
  p.vertices[i.val + 1]'(by have := i.isLt; omega)

theorem before_injective : Function.Injective p.before := by
  intro i j h
  apply Fin.ext
  exact p.nodup.getElem_inj_iff.mp h

theorem after_injective : Function.Injective p.after := by
  intro i j h
  apply Fin.ext
  have eq : i.val + 1 = j.val + 1 := p.nodup.getElem_inj_iff.mp h
  omega

theorem before_mem (i : p.EdgePosition) : p.before i ∈ p.vertices := List.getElem_mem _

theorem after_mem (i : p.EdgePosition) : p.after i ∈ p.vertices := List.getElem_mem _

private lemma split_slot (xs : List V) (i : ℕ) (h : i + 1 < xs.length) :
    xs = (xs.take i ++ [xs[i]'(by omega)]) ++ xs[i+1] :: xs.drop (i+2) := by
  have split := (List.take_append_drop (i+1) xs).symm
  rwa [List.take_succ_eq_append_getElem (by omega),List.drop_eq_getElem_cons h] at split

theorem split_at_edge (i : p.EdgePosition) :
    p.vertices = (p.vertices.take i.val ++ [p.before i]) ++
      p.after i :: p.vertices.drop (i.val+2) :=
  split_slot p.vertices i.val (by have := i.isLt; omega)

theorem split_at_two_edges (i j : p.EdgePosition) (gap : i.val + 1 < j.val) :
    ∃ (L M R : List V), p.vertices =
      (L ++ [p.before i]) ++ ((p.after i :: M) ++ [p.before j]) ++ (p.after j :: R) := by
  let D := p.vertices.drop (i.val+2)
  let k := j.val - (i.val+2)
  have add : i.val+2+k = j.val := by dsimp [k]; omega
  have kj : k+1 < D.length := by
    have h := j.isLt
    simp only [D,List.length_drop,k]
    omega
  have s := split_slot D k kj
  have first : D[k]'(by omega) = p.before j := by
    simp only [D,List.getElem_drop,add,before]
  have next : D[k+1] = p.after j := by
    simp only [D,List.getElem_drop,← Nat.add_assoc,add,after]
  rw [first,next] at s
  refine ⟨p.vertices.take i.val,D.take k,D.drop (k+2),?_⟩
  have eq := p.split_at_edge i
  change p.vertices =
    (p.vertices.take i.val ++ [p.before i]) ++ p.after i :: D at eq
  rw [s] at eq
  simpa only [List.cons_append,List.append_assoc] using eq

variable [DecidableEq V]

theorem predecessor_not_neighbor (noTrace : ¬ Catalogue.Traceable G)
    (i : p.EdgePosition) (hi : G.Adj z (p.after i)) : ¬ G.Adj z (p.before i) := by
  intro e
  have split : p.vertices = p.vertices.take i.val ++ p.before i :: p.after i ::
      p.vertices.drop (i.val+2) := by
    simpa only [List.append_assoc,List.singleton_append] using p.split_at_edge i
  exact (omission_constraints noTrace p).transitionOff _ _ _ _ split ⟨e,hi⟩

theorem terminal_not_adj_predecessor (noTrace : ¬ Catalogue.Traceable G)
    (i : p.EdgePosition) (hi : G.Adj z (p.after i)) : ¬ G.Adj p.last (p.before i) :=
  fun e => noTrace (traceable_of_terminal_predecessor p (p.split_at_edge i) hi.symm e.symm)

theorem predecessors_nonadjacent (noTrace : ¬ Catalogue.Traceable G)
    (i j : p.EdgePosition) (hi : G.Adj z (p.after i)) (hj : G.Adj z (p.after j)) :
    ¬ G.Adj (p.before i) (p.before j) := by
  intro e
  have ordered (r s : p.EdgePosition) (hr : G.Adj z (p.after r)) (hs : G.Adj z (p.after s))
      (less : r.val < s.val) (chord : G.Adj (p.before r) (p.before s)) : False := by
    have gap : r.val + 1 < s.val := by
      by_contra! close
      have eq : r.val + 1 = s.val := by omega
      have cross : p.after r = p.before s := by
        simp only [after,before,eq]
      exact p.predecessor_not_neighbor noTrace s hs (cross ▸ hr)
    obtain ⟨L,M,R,split⟩ := p.split_at_two_edges r s gap
    exact noTrace (traceable_of_predecessor_chord p split hr.symm hs chord)
  rcases lt_trichotomy i.val j.val with lt|eq|gt
  · exact ordered i j hi hj lt e
  · exact e.ne (congrArg p.before (Fin.ext eq))
  · exact ordered j i hj hi gt e.symm

omit [DecidableEq V] in
theorem before_ne_last (i : p.EdgePosition) : p.before i ≠ p.last := by
  intro eq
  have n := i.isLt
  have getLast : p.last = p.vertices[p.vertices.length-1]'(by omega) :=
    List.getLast_eq_getElem p.nonempty
  rw [getLast] at eq
  have pos : i.val = p.vertices.length - 1 := p.nodup.getElem_inj_iff.mp eq
  omega

/-- Every neighbor of the omitted vertex has a preceding edge
position, because the first vertex cannot be a neighbor. -/
theorem neighbor_has_position (noTrace : ¬ Catalogue.Traceable G)
    {v : V} (h : G.Adj z v) : ∃ i : p.EdgePosition, p.after i = v := by
  have mem := (p.covers v).mpr h.ne.symm
  obtain ⟨k,hk,atK⟩ := List.mem_iff_getElem.mp mem
  have pos : 0 < k := by
    by_contra! np
    have k0 : k = 0 := by omega
    subst k
    have first : p.first = v := (List.head_eq_getElem p.nonempty).trans atK
    exact (omission_constraints noTrace p).firstOff (first.symm ▸ h)
  let i : p.EdgePosition := ⟨k-1,by omega⟩
  refine ⟨i,?_⟩
  have eq : i.val+1 = k := by dsimp [i]; omega
  simpa only [after,eq] using atK

variable [DecidableRel G.Adj]

def flankIndices : Finset p.EdgePosition := Finset.univ.filter (fun i => G.Adj z (p.after i))

/-- Predecessors of the omitted vertex's neighbors. -/
def predecessors : Finset V :=
  p.flankIndices.map ⟨p.before,p.before_injective⟩

omit [DecidableEq V] in
theorem mem_predecessors {v : V} : v ∈ p.predecessors ↔
    ∃ i : p.EdgePosition, G.Adj z (p.after i) ∧ p.before i = v := by
  simp [predecessors,flankIndices]

variable [Fintype V]

theorem predecessors_card (noTrace : ¬ Catalogue.Traceable G) :
    p.predecessors.card = G.degree z := by
  have eq : p.flankIndices.map ⟨p.after,p.after_injective⟩ = G.neighborFinset z := by
    ext v
    simp only [flankIndices,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
      Function.Embedding.coeFn_mk,G.mem_neighborFinset]
    constructor
    · rintro ⟨i,e,rfl⟩
      exact e
    · intro e
      obtain ⟨i,eq⟩ := p.neighbor_has_position noTrace e
      exact ⟨i,eq.symm ▸ e,eq⟩
  rw [← G.card_neighborFinset_eq_degree,← eq,predecessors,Finset.card_map,Finset.card_map]

end PathOn

#print axioms PathOn.predecessors_nonadjacent
#print axioms PathOn.predecessors_card

end Graffiti199Depleted
