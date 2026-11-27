import DepletedPaths
import PairTerminal
import Mathlib.Tactic.FinCases

namespace Graffiti199Depleted

open Graffiti199K2.NearPacking.Depleted
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The four low vertices in the inner region have only their specified
neighbors. The half labels in the third and fourth rows are the four
high vertices reassigned from the depleted pair. -/
def innerLowNeighbors (r : Row) (i : K) : Option (List K) :=
  match i with
  | 0 => some [1,2,3]
  | 4 => some [5,6,7]
  | 8 => some [9,inside (halves r).1,inside (halves r).2.1]
  | 9 => some [8,inside (halves r).2.2.1,inside (halves r).2.2.2]
  | _ => none

def terminalLowNeighbors (i : O) : Option (List O) :=
  match i with
  | 0 => some [1,2,3]
  | 1 => some [0,4,5]
  | _ => none

abbrev innerRegion (f : K ↪ V) : Set V := {v | ∃ i, f i = v}

/-- The labelled graph data for the two-singleton and depleted-pair region.
The terminal pair retains every vertex when loss is false and every
vertex except its label 3 when loss is true. -/
structure NormalizedDepleted (G : SimpleGraph V) (loss : Bool) where
  inner : K ↪ V
  terminal : O ↪ V
  row : Row
  innerEdges : ∀ a b, (a,b) ∈ edges row false → G.Adj (inner a) (inner b)
  innerNonedges : ∀ a b, (a,b) ∈ forbidden → ¬ G.Adj (inner a) (inner b)
  innerLow : ∀ a ns, innerLowNeighbors row a = some ns →
    ∀ v, G.Adj (inner a) v → ∃ i ∈ ns, inner i = v
  terminalEdges : ∀ a b, (a,b) ∈ Graffiti199Depleted.terminalEdges →
    G.Adj (terminal a) (terminal b)
  terminalLow : ∀ a ns, terminalLowNeighbors a = some ns →
    ∀ v, G.Adj (terminal a) v → ∃ i ∈ ns, terminal i = v
  separate : Disjoint (innerRegion inner) (terminalRegion terminal loss)
  cover : ∀ v, v ∈ innerRegion inner ∨ v ∈ terminalRegion terminal loss

variable {loss : Bool} (L : NormalizedDepleted G loss)

private theorem inner_index_cases (r : Row) (i : K) :
    (∃ k : I, i = inside k ∧ high k = true) ∨ ∃ ns, innerLowNeighbors r i = some ns := by
  fin_cases i
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inl ⟨1,rfl,rfl⟩
  · exact Or.inl ⟨2,rfl,rfl⟩
  · exact Or.inl ⟨3,rfl,rfl⟩
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inl ⟨5,rfl,rfl⟩
  · exact Or.inl ⟨6,rfl,rfl⟩
  · exact Or.inl ⟨7,rfl,rfl⟩
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inr ⟨_,rfl⟩

theorem NormalizedDepleted.possible : possible L.row = true := by
  apply List.all_eq_true.mpr
  rintro ⟨a,b⟩ off
  have no : ¬ has (edges L.row false) a b = true := by
    intro h
    simp only [has,Bool.or_eq_true,List.contains_iff_mem] at h
    exact L.innerNonedges a b off (h.elim (L.innerEdges a b) (fun e => (L.innerEdges b a e).symm))
  cases h : has (edges L.row false) a b
  · rfl
  · exact (no h).elim

theorem NormalizedDepleted.inner_path
    {b : Bool} {i : I}
    (extra : b = true → G.Adj (L.inner 3) (L.inner 7))
    (ok : paths L.row b i ≠ []) :
    ∃ p : PathOn G (innerRegion L.inner), p.last = L.inner (inside i) := by
  let xs := paths L.row b i
  have v : valid (edges L.row b) i xs = true := paths_valid L.row b i L.possible ok
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
  obtain ⟨⟨⟨nd,all⟩,chain⟩,last⟩ := v
  have required (a c : K) (e : (a,c) ∈ edges L.row b) : G.Adj (L.inner a) (L.inner c) := by
    cases b
    · exact L.innerEdges a c e
    · change (a,c) ∈ edges L.row false ++ [(3,7)] at e
      rcases List.mem_append.mp e with e|e
      · exact L.innerEdges a c e
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp e)
        exact extra rfl
  have ch := chain.imp (fun a c e => by
    simp only [has,Bool.or_eq_true,List.contains_iff_mem] at e
    exact e.elim (required a c) (fun f => (required c a f).symm))
  let p : PathOn G (innerRegion L.inner) :=
    ⟨xs.map L.inner,by simpa using ok,(List.chain'_map _).mpr ch,nd.map L.inner.injective,fun v => by
      constructor
      · intro h
        obtain ⟨a,_,e⟩ := List.mem_map.mp h
        exact ⟨a,e⟩
      · rintro ⟨a,rfl⟩
        exact List.mem_map.mpr ⟨a,List.contains_iff_mem.mp
          (List.all_eq_true.mp all a (List.mem_finRange _)),rfl⟩⟩
  refine ⟨p,?_⟩
  apply Option.some.inj
  change some (p.vertices.getLast p.nonempty) = some (L.inner (inside i))
  rw [← List.getLast?_eq_getLast p.nonempty]
  change (xs.map L.inner).getLast? = _
  simp [last]

private theorem NormalizedDepleted.no_inner_terminal {v : V}
    (iv : v ∈ innerRegion L.inner) {i : O} (hi : terminalKept loss i = true) :
    L.terminal i ≠ v :=
  fun e => Set.disjoint_left.mp L.separate iv ⟨i,hi,e⟩

/-- An edge leaving a spanning path of the inner block can be used to
join a spanning path of the terminal block. A contact at low 0 uses
the retained triangle port when the other port was reassigned. -/
theorem NormalizedDepleted.finish_with_contact (p : PathOn G (innerRegion L.inner))
    {v : V} (vt : v ∈ terminalRegion L.terminal loss) (pv : G.Adj p.last v) :
    Nonempty (PathOn G Set.univ) := by
  obtain ⟨i,hi,rfl⟩ := vt
  have fromHigh {j : O} (jh : terminalHigh j = true) (jk : terminalKept loss j = true)
      (e : G.Adj p.last (L.terminal j)) : Nonempty (PathOn G Set.univ) := by
    obtain ⟨q,first⟩ := terminal_path_from_high L.terminal loss L.terminalEdges jk jh
    have cover : innerRegion L.inner ∪ terminalRegion L.terminal loss = Set.univ :=
      Set.eq_univ_of_forall L.cover
    exact ⟨cover ▸ p.join q L.separate (first.symm ▸ e)⟩
  have keep0 : terminalKept loss 0 = true := by cases loss <;> rfl
  have keep1 : terminalKept loss 1 = true := by cases loss <;> rfl
  have keep2 : terminalKept loss 2 = true := by cases loss <;> rfl
  have keep4 : terminalKept loss 4 = true := by cases loss <;> rfl
  have keep5 : terminalKept loss 5 = true := by cases loss <;> rfl
  fin_cases i
  · obtain ⟨j,jm,je⟩ := L.terminalLow 0 [1,2,3] rfl p.last pv.symm
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 by simpa using jm) with rfl|rfl|rfl
    · exact (L.no_inner_terminal p.last_mem keep1 je).elim
    · exact (L.no_inner_terminal p.last_mem keep2 je).elim
    · exact fromHigh (j := 2) rfl keep2 (je ▸ (L.terminalEdges 2 3 (by decide)).symm)
  · obtain ⟨j,jm,je⟩ := L.terminalLow 1 [0,4,5] rfl p.last pv.symm
    rcases (show j = 0 ∨ j = 4 ∨ j = 5 by simpa using jm) with rfl|rfl|rfl
    · exact (L.no_inner_terminal p.last_mem keep0 je).elim
    · exact (L.no_inner_terminal p.last_mem keep4 je).elim
    · exact (L.no_inner_terminal p.last_mem keep5 je).elim
  · exact fromHigh rfl hi pv
  · exact fromHigh rfl hi pv
  · exact fromHigh rfl hi pv
  · exact fromHigh rfl hi pv

private def innerHighMap : I ↪ K :=
  ⟨inside,fun _ _ h => Fin.ext (congrArg (fun x : K => x.val) h)⟩

/-- Three available inner high endpoints suffice. Delete only the other highs,
keeping the low edge on each side of the cut. -/
theorem NormalizedDepleted.traceable_of_small_blocked
    (reach : EdgeReachAfterSmallDeletion G)
    {b : Bool} (extra : b = true → G.Adj (L.inner 3) (L.inner 7))
    (small : (blocked L.row b).card ≤ 3) : Nonempty (PathOn G Set.univ) := by
  classical
  let h := innerHighMap.trans L.inner
  let D := (blocked L.row b).map h
  have dsmall : D.card ≤ 3 := by simpa [D] using small
  have survive_at_end (k : K) (large : 8 ≤ k.val) : L.inner k ∉ D := by
    intro hD
    obtain ⟨i,_,e⟩ := Finset.mem_map.mp hD
    have eq : inside i = k := L.inner.injective e
    have valEq : i.val = k.val := congrArg (fun j : K => j.val) eq
    have bound := i.isLt
    omega
  have outside_survives (i : O) (ke : terminalKept loss i = true) : L.terminal i ∉ D := by
    intro hD
    obtain ⟨k,_,e⟩ := Finset.mem_map.mp hD
    exact Set.disjoint_left.mp L.separate ⟨inside k,e⟩ ⟨i,ke,rfl⟩
  have keep0 : terminalKept loss 0 = true := by cases loss <;> rfl
  have keep1 : terminalKept loss 1 = true := by cases loss <;> rfl
  have ab : G.Adj (L.inner 8) (L.inner 9) := L.innerEdges 8 9 (by simp [edges])
  have cd : G.Adj (L.terminal 0) (L.terminal 1) := L.terminalEdges 0 1 (by decide)
  obtain ⟨u,ui,v,vo,uD,_,uv⟩ := crossingAfterSmallDeletion reach dsmall
    (U := innerRegion L.inner) ⟨8,rfl⟩
    (fun h => Set.disjoint_left.mp L.separate h ⟨0,keep0,rfl⟩)
    (survive_at_end 8 (by decide)) (survive_at_end 9 (by decide))
    (outside_survives 0 keep0) (outside_survives 1 keep1) ab cd
  have vt := (L.cover v).resolve_left vo
  obtain ⟨k,rfl⟩ := ui
  rcases inner_index_cases L.row k with ⟨i,rfl,ih⟩|⟨ns,nsEq⟩
  · have existsPath : paths L.row b i ≠ [] := fun e =>
      uD (Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ih,e⟩,rfl⟩)
    obtain ⟨p,last⟩ := L.inner_path extra existsPath
    exact L.finish_with_contact p vt (last.symm ▸ uv)
  · obtain ⟨l,_,eq⟩ := L.innerLow k ns nsEq v uv
    exact (vo ⟨l,eq⟩).elim

#print axioms NormalizedDepleted.inner_path
#print axioms NormalizedDepleted.finish_with_contact
#print axioms NormalizedDepleted.traceable_of_small_blocked

end Graffiti199Depleted
